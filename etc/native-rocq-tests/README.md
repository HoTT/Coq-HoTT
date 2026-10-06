# Testing the native Rocq toolchain

Run a project command without Coq compatibility executables on `PATH`:

```sh
python3 etc/without_coq_compat.py sh -c 'dune build theories/ test/ contrib/ && dune test'
```

Use a native Rocq package environment for a minimal-installation check. The
launcher preserves toolchain variables and native executable locations, filters
only directories containing compatibility names, and unsets `COQBIN` so it cannot
bypass the filtered path. Genuine third-party names such as `coq-lsp` are retained.
This tests executable discovery, not isolation from deliberately hard-coded
absolute paths.

For Make or wrapper smoke tests, prefix the corresponding command in the same
way. Configure the generated Makefile in the native environment as well; it
records the toolchain location. The ported compiler wrappers are tracked in
#2415. No project compiler flags are changed by this launcher.

The unit tests run through `dune test`. They can also be run directly:

```sh
python3 -m unittest discover -s etc/native-rocq-tests -v
```
