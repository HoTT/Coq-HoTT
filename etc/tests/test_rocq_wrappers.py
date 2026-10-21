import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ETC = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ETC))
import rocq_wrapper


class WrapperTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.log = self.root / 'calls.jsonl'
        self.vfile = self.root / 'file with spaces.v'
        self.vfile.write_text('unchanged\n')
        self.env = dict(os.environ, PATH=str(self.root) + os.pathsep + os.environ['PATH'],
                        FAKE_LOG=str(self.log), FAKE_RET='0',
                        COQC_SEARCH='NO_MATCH', COQC_REPLACE='')
        self.executable('rocq', "import json, os, sys\n"
                        "with open(os.environ['FAKE_LOG'], 'a') as f:\n"
                        "    f.write(json.dumps(sys.argv[1:]) + '\\n')\n"
                        "print('compiler stdout')\n"
                        "print('compiler stderr', file=sys.stderr)\n"
                        "sys.exit(int(os.environ['FAKE_RET']))\n")
        self.executable('pgrep', "import sys\nprint(2)\nsys.exit(0)\n")
        self.executable('coqc', "raise SystemExit('Unexpected legacy compiler invocation')\n")

    def executable(self, name, body):
        path = self.root / name
        path.write_text('#!' + sys.executable + '\n' + body)
        path.chmod(0o755)

    def invoke(self, name, args):
        prefix = ['bash'] if name.endswith('.sh') else [sys.executable]
        return subprocess.run(prefix + [str(ETC / name)] + args, env=self.env,
                              capture_output=True, text=True, timeout=10)

    def calls(self):
        return [json.loads(line) for line in self.log.read_text().splitlines()]

    def module(self, name):
        spec = importlib.util.spec_from_file_location(name, ETC / (name + '.py'))
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        return module

    def test_argument_dispatch(self):
        for args, command, files in [
            (['compile', '-noinit', 'a.v'], ['rocq', 'compile', '-noinit', 'a.v'], ['a.v']),
            (['c', 'a.v'], ['rocq', 'c', 'a.v'], ['a.v']),
            (['-noinit', 'a.v'], ['rocq', 'compile', '-noinit', 'a.v'], ['a.v']),
            (['doc', 'a.v'], ['rocq', 'doc', 'a.v'], []),
            (['--version'], ['rocq', '--version'], []),
            (['compile', '--version'], ['rocq', 'compile', '--version'], []),
        ]:
            self.assertEqual(rocq_wrapper.prepare_command(args), (command, files))

    def test_passthrough(self):
        for name in ('coqcreplace.py', 'coqcstriprequires.py', 'coqccount.sh'):
            for args in (['--version'], ['compile', '--version'], ['doc', str(self.vfile)]):
                with self.subTest(name=name, args=args):
                    if self.log.exists():
                        self.log.unlink()
                    self.env['FAKE_RET'] = '7'
                    result = self.invoke(name, args)
                    self.assertEqual(result.returncode, 7)
                    self.assertEqual(self.calls(), [args])
                    self.assertEqual(result.stdout, 'compiler stdout\n')
                    self.assertEqual(result.stderr, 'compiler stderr\n')
                    self.assertEqual(self.vfile.read_text(), 'unchanged\n')
                    self.assertFalse(Path(str(self.vfile) + '.bak').exists())

    def test_compile_forwarding_and_failure(self):
        args = ['compile', '-noinit', '-indices-matter', '-R', 'directory with spaces',
                'HoTT', str(self.vfile)]
        for name in ('coqcreplace.py', 'coqcstriprequires.py', 'coqccount.sh'):
            with self.subTest(name=name):
                if self.log.exists():
                    self.log.unlink()
                self.env['FAKE_RET'] = '9'
                result = self.invoke(name, args)
                self.assertEqual(result.returncode, 9)
                self.assertEqual(self.calls(), [args])
                self.assertIn('compiler stdout', result.stdout)
                self.assertIn('compiler stderr', result.stderr)
                self.assertFalse(Path(str(self.vfile) + '.bak').exists())

    def test_counting_and_compile_alias(self):
        args = ['c', str(self.vfile), '-q']
        result = self.invoke('coqccount.sh', args)
        self.assertEqual(result.returncode, 0)
        self.assertEqual(self.calls(), [args])
        self.assertIn('-> 2 ' + str(self.vfile), result.stderr)
        self.assertIn('<- 3 ' + str(self.vfile), result.stderr)

    def test_replacement_accepts_reverts_and_times_out(self):
        module = self.module('coqcreplace')
        self.vfile.write_text('GOOD\nBAD\nSLOW\n')
        module.coqc_search = re.compile('GOOD|BAD|SLOW')
        module.coqc_replace = r'\g<0>_CHANGED'

        def compiler(*args, **kwargs):
            text = self.vfile.read_text()
            status = 1 if 'BAD_CHANGED' in text else 1111 if 'SLOW_CHANGED' in text else 0
            return status, 0.5

        with patch.object(module, 'coqc', compiler):
            result = module.replace(str(self.vfile))
        self.assertEqual(result, (0, 1, 3, 1))
        self.assertEqual(self.vfile.read_text(), 'GOOD_CHANGED\nBAD\nSLOW\n')

    def test_import_stripping_accepts_reverts_and_times_out(self):
        module = self.module('coqcstriprequires')
        self.vfile.write_text('Require Import Keep Drop Slow.\n')

        def compiler(*args, **kwargs):
            text = self.vfile.read_text()
            status = 1 if 'Keep' not in text else 1111 if 'Slow' not in text else 0
            return status, 0.5

        with patch.object(module, 'coqc', compiler):
            result = module.striprequires(str(self.vfile))
        self.assertEqual(result, (0, 1, 3, 1))
        self.assertEqual(self.vfile.read_text(), 'Require Import Keep Slow.\n')

    def test_timeout_and_quiet_output(self):
        command = ['rocq', 'compile', 'a.v']
        with patch('rocq_wrapper.subprocess.run', side_effect=subprocess.TimeoutExpired(command, 1)):
            self.assertEqual(rocq_wrapper.run_compiler(command, timeout=1)[0], 1111)
        with patch('rocq_wrapper.subprocess.run') as run, \
                patch('rocq_wrapper.time.perf_counter', side_effect=[0, 2]):
            run.return_value.returncode = 0
            self.assertEqual(rocq_wrapper.run_compiler(command, quiet=True, timeout=1), (1111, 2))
            self.assertEqual(run.call_args.kwargs['stdout'], subprocess.DEVNULL)
            self.assertEqual(run.call_args.kwargs['stderr'], subprocess.DEVNULL)


if __name__ == '__main__':
    unittest.main()
