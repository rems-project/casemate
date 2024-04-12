pKVM simplified model sketch, in Coq, ported from C



### Install dependencies
Install base packages with opam:
```bash
opam install coq coq-lsp
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam install coq_stdpp coq-stdpp-bitvector
```

Install RecordUpdate:
```bash
git clone https://github.com/tchajed/coq-record-update.git
make -j 8
make install
```
