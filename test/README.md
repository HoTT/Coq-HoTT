# Tests

Here we collect tests from various issues and PRs.

## Adding a test

To add a test, create a new .v file in this directory. The file name should be
`github<issue number>.v` or `github<PR number>.v`. For example, if you are
adding a test for issue #123, the file name should be `github123.v`.

When testing properties of the library, try to keep the same directory
structure. For instance, tests about suspensions should be in
`Test/Homotopy/Suspension.v`.

## Running tests

To run the tests, simply run
```
dune test
```
from the root of the repository (or here).
 