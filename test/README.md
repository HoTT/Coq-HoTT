# Tests

Sometimes there are properties of the library that we would like to test
without polluting it with examples and noisy output. Such tests are collected
here.

We also collect regression tests from various issues and PRs in a
subdirectory called `bugs/`.

## Adding a test

To add a test, create a new .v file in a subdirectory of this directory.

When testing properties of the library, use the same directory
structure. For instance, tests about suspensions should be in
`test/Homotopy/Suspension.v`.

Place regression tests in the subdirectory `bugs`, using file name `github<issue
number>.v` or `github<PR number>.v`. For example, if you are adding a test for
issue #123, the file name should be `test/bugs/github123.v`.

## Running tests

To run the tests, simply run
```
dune test
```
