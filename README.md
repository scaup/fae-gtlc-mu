# blabla
blablabla

# Requirements

Coq: 8.11.1
IRIS version: dev.2020-04-07.7.64bed0ca
coq-autosubs: dev.coq86

## Getting started quickly with opam

Get opam.
http://opam.ocaml.org/doc/Install.html

Optionally, create a new switch.
```
opam switch create fae ocaml-base-compiler.4.09.0
``` 
Add coq and iris-dev repositories.
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
``` 
Install iris and autosubst.
```
opam install coq-iris.dev.2020-04-07.7.64bed0ca
opam install coq-autosubst.dev.coq86
```
Compile by running `make` in the root of this project.
