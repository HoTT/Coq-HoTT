## Elementary git usage. 
This is in addition to the instructions on how to set up git in `INSTALL.md`

USAGE 1: add + commit

To have git record your changes:

` git commit -m "description of edit" <files-you-changed>`

USAGE 2: pull

To pull changes by others from GitHub:

(Your local directory will still have your changes.)

We call the central repo "upstream"

`git add remote upstream https://github.com/HoTT/HoTT.git`

 FIRST commit your changes as above, then

`git pull upstream master`

(This is the central repo)

USAGE 3: compile + push

See [Contributing](https://github.com/HoTT/HoTT/blob/master/STYLE.md)

To push your changes to GitHub:

FIRST, commit your changes as above

SECOND, pull changes from GitHub as above, then

```
make -j2
git push origin master
```

(This is your own repo)

Now go to your github page and click create pull request.
This will then be compiled (again) by Travis and reviewed by the developers.
After github discussion, and possible updates of the pull request, 
one of them will pull your request.

Which files did I change since the last commit?

`git status`

What changes did I make in those files?

`git diff`

Who wrote in this file?

`git praise`

Rewrite your master branch so that any commits of yours that
aren't already in upstream/master are replayed on top of that
other branch. See also [STYLE](https://github.com/HoTT/HoTT/blob/master/STYLE.md)

`git rebase upstream/master`

If you've rebased your branch onto upstream/master you may need to force the push in order to push it to  your own forked repository on GitHub. You'd do that with:

`git push -f origin master`

Stash your local changes when you are not happy with them

`git stash`

When all else fails, get a fresh copy from your own clone on github.

`git reset --hard origin/master`

We have our own version of Coq in a git submodule. When it is updated upstream run:

`etc/install_coq.sh`
or by hand:

`cd coq-HoTT && make clean && cd ..`

(or even `cd coq-HoTT && git clean -xfd && cd ..`).

Then

`git submodule update && cd coq-HoTT && ./configure -local && make -j2 -k coqide coqlight`

For more, there are [plenty][1] of [tutorials][2] online.
[1]: https://www.atlassian.com/git/tutorials/
[2]: http://git-scm.com/docs/gittutorial
