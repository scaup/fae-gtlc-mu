# full abstraction results for the embedding of STLCmu into GTLCmu (Coq/Iris proof)

This repo contains Coq/Iris proofs for full abstraction results of the embedding of STLCmu (the simply typed lambda calculus with equirecursive types) into GTLCmu (its gradualization).

## Requirements for compiling

- Coq: 8.11.1
- Coq libraries
  * stdpp: dev.2020-04-03.1.eeef6250
  * IRIS: dev.2020-04-07.7.64bed0ca
  * coq-autosubs: dev.coq86

## Getting started quickly with opam

Get opam: http://opam.ocaml.org/doc/Install.html
> The quickest way to get the latest opam up and working is to run this script:
```
sh <(curl -sL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)
```
Don't forget to add the directory of installation to your path!
Initialize opam.
```
$ opam init
$ eval $(opam env) # optionally; see output of previous command
```
Create a new switch with the ocaml-base-compiler.4.09.0.
```
$ opam switch create fae ocaml-base-compiler.4.09.0
$ opam switch # output should be like: → fae
``` 
Add coq and iris-dev repositories to this switch.
```
$ opam repo add coq-released https://coq.inria.fr/opam/released
$ opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
``` 
Install Coq and the required libraries.
```
$ opam install coq.8.11.1 coq-stdpp.dev.2020-04-03.1.eeef6250 coq-iris.dev.2020-04-07.7.64bed0ca coq-autosubst.dev.coq86
```
Optionally, you can also install coqide, a GUI to interact with the Coq code.
```
$ opam install coqide.8.11.1
```
Verify that installation went OK
```
$ opam list # output should list the required packages with the right versions
$ which coqc # verify that coqc is in your path, if not, run "eval $(opam env)"
$ coqc --version # should return 8.11.1, and "compiled on" should be realistic
$ coqc --config # check the COQLIB=~/.opam/fae/lib/coq/ variable
$ ls ~/.opam/fae/lib/coq/user-contrib # should return the Autosubst, iris, Ltac2 and stdpp directories
```
Compile by running `make` in the root of this project.
```
$ make
```
## Verifying the main results only

Files related to the definition of stlc_mu:
```
theories/stlc_mu/lang.v # dynamics
theories/stlc_mu/types.v # types
theories/stlc_mu/typing.v # typing derivations
theories/stlc_mu/contexts.v # (general) contexts + definition contextual equivalence
```
Files related to the definition of the cast calculus:
```
theories/cast_calculus/types.v # types
theories/cast_calculus/consistency/standard.v # the (conventional) consistency relation
theories/cast_calculus/lang.v # dynamics
theories/cast_calculus/typing.v # typing derivations
theories/cast_calculus/contexts.v # contexts  + definition contextual equivalence
```
Files related to the embedding from stlc_mu to the cast_calculus:
```
theories/embedding/expressions.v
theories/embedding/contexts.v
theories/embedding/types.v
theories/embedding/well_typedness.v # well-typedness of embedding
```
The file `theories/two_fa_a.v` proves 2FA-A for the embedding.
The file `theories/one_fa_d.v` proves 1FA-D for the embedding.
The file `theories/tow_fa_d.v` proves 2FA-D for the embedding.

## Proof structure (where's what?)
Cool, so you're actually interested in the proof itself!

The following files relate to the backtranslation:
```
theories/backtranslation/cast_help/universe.v # defines universe type
theories/backtranslation/types.v # back-translation on types
theories/cast_calculus/consistency/structural.v # alternative consistency relation
theories/backtranslation/cast_help/general.v # backtranslation of casts by induction on alternative consistency (collects other files in that directory)
theories/cast_calculus/consistency/equivalence/proof.v # proof that conventional consistency implies alternative consistency (collects other files in that directory)
theories/backtranslation/expressions.v # backtranslation on expressions (using aforementioned proof)
theories/backtranslation/contexts.v # backtranslation on contexts
theories/backtranslation/well_typedness.v # well-typedness backtranslation
```
Files related to the (static <= gradual)-logical relations:
```
theories/refinements/static_gradual/resources_left.v # Iris resources for static part
theories/refinements/static_gradual/resources_right.v # Iris resources for gradual part
theories/refinements/static_gradual/logical_relation.v # definition (static <= gradual) logical relations
theories/refinements/static_gradual/compat_easy.v # unexciting compat lemmas (fig 12 in paper)
theories/refinements/static_gradual/compat_cast/defs.v # defines generalized compat lemma for casts
theories/refinements/static_gradual/compat_cast/all.v # proof of generalized compat lemma casts (collects other files in that directory)
theories/refinements/static_gradual/rel_ref_specs.v # collects compat lemmas for lemma 4.2 in paper
theories/refinements/static_gradual/adequacy.v # lemma 4.3 in paper
```
Files related to the (gradual <= static)-logical relations:
```
theories/refinements/gradual_static/resources_left.v # Iris resources for the gradual part
theories/refinements/gradual_static/resources_right.v # Iris resources for the static part
theories/refinements/gradual_static/logical_relation.v # definition (gradual <= static) logical relations
theories/refinements/gradual_static/compat_easy.v # unexciting compat lemmas (counterpart to fig 12 in paper)
theories/refinements/static_gradual/compat_cast/defs.v # defines generalized compat lemma for casts
theories/refinements/static_gradual/compat_cast/all.v # proof of generalized compat lemma casts (collects other files in that directory)
theories/refinements/gradual_static/rel_ref_specs.v # collects compat lemmas for lemma 4.4 in paper
theories/refinements/gradual_static/adequacy.v # lemma 4.5 in paper
```

## Credits
Lots of code has its origin in the following;
https://gitlab.mpi-sws.org/iris/examples/-/tree/master/theories/logrel/F_mu_ref_conc
