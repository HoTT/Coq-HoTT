import contextlib
import importlib.util
import io
import os
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "without_coq_compat.py"
spec = importlib.util.spec_from_file_location("without_coq_compat", SCRIPT)
launcher = importlib.util.module_from_spec(spec)
spec.loader.exec_module(launcher)


class NativeEnvironmentTests(unittest.TestCase):
    def executable(self, directory, name):
        path = Path(directory) / name
        path.write_text("#!/bin/sh\nexit 0\n")
        path.chmod(0o755)
        return path

    def test_excludes_compat_not_third_party_tools(self):
        with tempfile.TemporaryDirectory() as directory:
            for name in launcher.COMPAT | {"rocq", "rocqworker", "coq-lsp", "fcc"}:
                self.executable(directory, name)
            with launcher.native_environment({"PATH": directory, "COQBIN": directory,
                                               "OCAMLPATH": "retained"}) as env:
                for name in launcher.COMPAT:
                    self.assertIsNone(shutil.which(name, path=env["PATH"]))
                for name in ("rocq", "rocqworker", "coq-lsp", "fcc"):
                    self.assertIsNotNone(shutil.which(name, path=env["PATH"]))
                self.assertNotIn("COQBIN", env)
                self.assertEqual(env["OCAMLPATH"], "retained")
                filtered = env["PATH"]
            self.assertFalse(Path(filtered).exists())

    def test_precedence_and_missing_directories(self):
        with tempfile.TemporaryDirectory() as first, tempfile.TemporaryDirectory() as second:
            original = self.executable(first, "rocq")
            self.executable(second, "rocq")
            with launcher.native_environment({"PATH": os.pathsep.join(
                    [first, first + "/missing", second])}) as env:
                self.assertEqual(Path(shutil.which("rocq", path=env["PATH"])).resolve(),
                                 original.resolve())

    def test_arguments_and_exit_status(self):
        status = launcher.main([sys.executable, "-c",
                                'import sys; assert sys.argv[1] == "with spaces"; sys.exit(7)',
                                "with spaces"])
        self.assertEqual(status, 7)

    def test_missing_command_and_usage(self):
        with contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(launcher.main(["hott-nonexistent-command"]), 127)
            self.assertEqual(launcher.main([]), 2)


if __name__ == "__main__":
    unittest.main()
