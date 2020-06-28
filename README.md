# What's here?

A Coq/Iris proof for the FAE-criterion for GTLC\mu (the embedding from STLC\mu into GTLC\mu is fully abstract).
It accompanies the paper "Fully abstract from Static to Gradual"

# Requirements for compiling

Coq: 8.11.1
IRIS version: dev.2020-04-07.7.64bed0ca
coq-autosubs: dev.coq86

## Doing your own thing

Make sure you have the right versions of Coq and the required libraries in path.
The directory contains a `Makefile`, activated by running `make` in the root of this directory.

## Getting started quickly with opam

Get opam.
http://opam.ocaml.org/doc/Install.html

Create a new switch with the ocaml-base-compiler.4.09.0.
```
opam switch create fae ocaml-base-compiler.4.09.0
``` 
Add coq and iris-dev repositories.
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
``` 
Install the right versions of iris and autosubst.
```
opam install coq-iris.dev.2020-04-07.7.64bed0ca
opam install coq-autosubst.dev.coq86
```

Make sure that the right Coq in scope..
```
eval $(opam env) # adds the installed coq with libs to your path
coqc --version # should return 8.11.1, and "compiled on" should be just now..

```
Compile by running `make` in the root of this project.

# Verifying the main result only

Go through the following files if you only want to verify the FAE-claim for the embedding.

```
theories/stlc_mu/lang.v # definition stlc_mu
theories/stlc_mu/types.v # types for stlc_mu
theories/stlc_mu/typing.v # typing derivations for stlc_mu

```

todo

# Proof structure (where's what?)

todo

# Credit to

Lots of code has its origin in the following;
https://gitlab.mpi-sws.org/iris/examples/-/tree/master/theories/logrel/F_mu_ref_conc
