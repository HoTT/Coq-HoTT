# GitHub Copilot Instructions

Follow [AGENTS.md](../AGENTS.md).

## Environment Setup

The Nix development shell is not activated automatically, so prefix project
commands with `nix develop -c`:

```sh
nix develop -c dune build
nix develop -c dune test
```
