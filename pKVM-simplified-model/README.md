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

### Extracting traces that can be parsed

To extract logs of the right format, a few options have to be set correctly for compiling the linux kernel.  the options `Runtime simplified model checking` and `Colours in the output of nVHE ghost spec` have to be enabled. Optionally, the option `Only log simplified model steps` can be enabled.
