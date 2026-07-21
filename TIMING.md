**Timing:**

This file contains miscellanous information about how to time the building of the library in various ways.

A few best practices for timing:

- It's important to have an idle machine, so stop other processes, including browsers.

- Timing also is affected by thermal issues on some machines (particularly laptops).

- It may help to be on A/C power, depending on the machine.

Methods for timing overall builds.
Unless said otherwise, all of the commands should be run from the top-level repo dir, above the theories dir.

- To get overall build time, can use:

    ```
    dune clean; make clean > /dev/null 2>&1; sync; sleep 8
    time nice -n -10 dune build --cache=disabled --display=quiet
    ```

  It's important to use `--display=quiet`, as dune itself uses a non-trivial amount of cpu with its default display.
  The `nice -n -10` might require special privileges.  Using a negative number gives *extra* priority to the job.  You can just omit this if not available.

- Or, if you want to use `make` to get overall time, use:

    ```
    make clean > /dev/null 2>&1; sync; sleep 8
    time nice -n -10 make -j<num_cores> > /dev/null
    ```

  Adjust "-j<num_cores>" based on the number of cores you have and thermal throttling limits.

- If you want several samples:

    ```
    hyperfine --runs <N> -p 'dune clean; make clean > /dev/null 2>&1; sync; sleep 30' 'nice -n -10 dune build --cache=disabled --display=quiet'
    ```

  The sleep helps with thermal issues on my machine.

It's often better to get per file timing, as it's easier to see changes that way.  The [coq-scripts repository](https://github.com/JasonGross/coq-scripts) can help with this.  For some reason, it needs to be within the repo you are timing.  I clone it into the top-level dir of the HoTT repo.  See [coq-scripts/timing/README.md](https://github.com/JasonGross/coq-scripts/tree/master/timing) within that repo for documentation.

- If new changes are already committed and nothing is changed or staged, you can use the following.  Note that "tip" is a misnomer; it compares whatever is currently checked out (even in "detached head" state), to the previous commit or `PREV_COMMIT`.

    ```
    export PREV_COMMIT=<hash>   [defaults to previous commit]
    export PREV_COMMIT=master   [etc.]
    make -j<num_cores>
    nice -n -10 ./coq-scripts/timing/make-pretty-timed-only-diff-tip.sh -j1  [or -jJ]
    sort -r -k 12 time-of-build-both.log | less   [biggest changes first]
    sort -r -k  1 time-of-build-both.log | less   [slowest files first]
    ```

  With `only-diff`, it only compares changed files and their dependencies. If you instead use `diff`, it compares all files.

  `-j1` gives more precise timing, but takes longer.  Again, this depends partly on thermal issues.

  If you are using `-j1` and `only-diff`, run `make -j8` first, since it starts by making sure the current tree is up-to-date, and there's no need to use -j1 for that step.

- If new changes are not committed, stage them, and do:

    ```
    nice -n -10 ./coq-scripts/timing/make-pretty-timed-only-diff.sh -j1  [or -jJ]
    sort -r -k 12 time-of-build-both.log | less
    ```

  Same comments about `only-diff` and `diff`, `-j1`, etc.

- To show the timing for the current working directory (no comparison), e.g. to search for slow files:

    ```
    nice -n -10 ./coq-scripts/timing/make-pretty-timed.sh -j1  [or -jJ]
    less time-of-build-pretty.log
    ```

Other timing methods:

- To get the timing for a single file using `hyperfine` (which does multiple runs and gives stats), can do this via a special `dune` rule:

    ```
    echo '(theories/WildCat/Equiv.v)' > file_to_bench
    dune build @bench
    ```

- To show the time for each line in a file, do:

    ```
    make timing-html/HoTT.Modalities.ReflectiveSubuniverse.html 
    ```

  and then view that file in a browser.

- For any Coq project, can do

    ```
    rm time-of-build.log  [optional; gets appended to]
    make clean            [optional; depends whether you want to time only changed files]
    make pretty-timed
    ```

  to see a nice summary of the user time for each file, sorted.  Saved in time-of-build.log and time-of-build-pretty.log.  Add `TIMING_REAL=1` to see real time instead.  Can also compare revisions, etc.  See

    https://coq.inria.fr/refman/practical-tools/utilities.html#timing-targets-and-performance-testing

- To find the slowest lines in the whole library:

    ```
    make [-jJ]
    cd theories [or subdir to limit search]
    find . -name '*.v.timing' -exec awk '{printf "%-55s %s\n", "{}:", $0}' {} \; | sort -nr -k7 | head -20 | sed 's/.v.timing//'
    ```

  Locations are indicated by character position with the file.  In emacs, can use `M-x goto-char NNN RET` to find the spot.

Currently, most fine-grained timing tests have to be done using `make` instead of `dune`.  See https://github.com/ocaml/dune/issues/11587 for a feature request to add this support to dune.
