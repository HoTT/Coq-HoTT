# Tests

Sometimes there are some properties about the library that we would like to test
without polluting it with examples and noisy output. Such tests are collected
here.

Here we also collect regression tests from various issues and PRs in a
subdirectory called `bugs/`.

## Adding a test

To add a test, create a new .v file in this directory.

When testing properties of the library, try to keep the same directory
structure. For instance, tests about suspensions should be in
`Test/Homotopy/Suspension.v`.


For regression tests, the file name should be `github<issue number>.v` or
`github<PR number>.v`. For example, if you are adding a test for issue #123, the
file name should be `github123.v` and they should be placed in `bugs/`.

## Running tests

To run the tests, simply run
```
dune test
```
from the root of the repository (or here).
 