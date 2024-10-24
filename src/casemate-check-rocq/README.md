Casemate offline checker in Coq. Ported from C.

## Building

First, register additional repositories with your Opam switch:

```bash
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam pin add --no-action https://github.com/tchajed/coq-record-update.git
```

(Press `y` at prompts.)

After that, either install `casemate` by running:

```bash
opam install .
```

Or install just the dependencies (e.g. for development) by running:

```bash
opam install --deps-only .
```
