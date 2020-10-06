# the embedding of STLCmu into GTLCmu is fully abstract (Coq/Iris proof)

This repo contains a Coq/Iris proof of the fact that the embedding of STLCmu (the simply typed lambda calculus with equirecursive types) into GTLCmu (its gradualization) is fully abstract.
It accompanies the paper  "Fully abstract from Static to Gradual".

## VM-Image for artifact evaluation

For the purpose of artifact evaluation, a vm-image was created and can be found at ...
It contains the compiled Coq code of this repository, some tools to interact with the Coq code (e.g. CoqIDE), and extra documentation.

## Requirements for compiling coq code

- Coq: 8.11.1
- Coq libraries
  * stdpp: dev.2020-04-03.1.eeef6250
  * IRIS: dev.2020-04-07.7.64bed0ca
  * coq-autosubs: dev.coq86

## Getting started quickly with opam

An easy way to get the correct version of Coq and the required libraries is by using opam.

Get opam (http://opam.ocaml.org/doc/Install.html), by fetching and running the install script.
You need curl for this (e.g. `apt install curl`).
```
sh <(curl -sL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)
```
Don't forget to add the directory of installation to your path such that you don't have to refer to opam by its full path.
Initialize opam.
```
$ opam init
$ eval $(opam env) # optionally; see output of previous command
```
Create a new switch with the ocaml-base-compiler.4.09.0.
To do this, you need some base dependencies: make m4 cc (e.g. `apt install make m4 gcc`).
```
$ opam switch create fae ocaml-base-compiler.4.09.0
$ opam switch # output should be like: → fae
``` 
Add coq and iris-dev repositories to this switch.
For the iris-dev repo, you need to have git (e.g. `apt install git`).
```
$ opam repo add coq-released https://coq.inria.fr/opam/released
$ opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
``` 
Install the correct version of Coq and the required libraries.
```
$ opam install coq.8.11.1 coq-stdpp.dev.2020-04-03.1.eeef6250 coq-iris.dev.2020-04-07.7.64bed0ca coq-autosubst.dev.coq86
```
Optionally, you can also install coqide, a GUI to interact with the Coq code.
```
$ opam install coqide.8.11.1 # will likely ask you to install missing dependencies
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
## Verifying the full abstraction claim

This section describes the files necessary to go through in order to verify that full abstraction is indeed proven for the embedding from STLCmu to GTLCmu.

### Verifying definition of the simply typed lambda calculus with iso-recursive types

The links in this section are relative to `theories/stlc_mu/`.
- [theories/stlc_mu/lang.v](lang.v) starts by defining the expressions and values;
for this we use De Bruijn indices, utilizing [https://www.ps.uni-saarland.de/autosubst/doc/manual.pdf](Autosubst) to do so (detailed knowledge is not required).
Afterwards, it defines evaluation contexts (of depth 1) and head step reductions.
The final language is defined using the `EctxiLanguage` construct from the Iris library; essentially, it naturally defines the general evaluation contexts and the total reduction relation.
Lastly, we define the `Halts` predicative for expressions.
- [theories/stlc_mu/types.v](types.v) defines the static types (again using Autosubst).
- [theories/stlc_mu/typing.v] defines the typing rules for expressions.
We restrict our typing derivations so that they only treat meaningful types; the closed types (types with no free variables) (see [theories/prelude.v] for the formal definition of closedness).
- [theories/stlc_mu/contexts.v](contexts.v) defines general contexts (not evaluation contexts) together with their typing rules.
- [theories/stlc_mu/ctx_equiv.v](ctx_equiv.v) defines contextual equivalence.

### Verifying definition of the cast calculus of GTLCmu

The links in this section are relative to `theories/cast_calculus/`.
- [theories/cast_calculus/types.v](types.v) defines the gradual types, ground types, the shape operator (S in figure 2 of paper) and type `ICP` to encode inert pairs (two function types or a ground and unknown type) which is used in [theories/cast_calculus/lang.v](lang.v) to define which expressions are values.
- [theories/cast_calculus/types_notations.v] defines some handy notations for types.
- [theories/cast_calculus/lang.v](lang.v) defines expressions, values, evaluation contexts, head reductions, total reduction, and a `Halts` predicate on expressions.
- [theories/cast_calculus/consistency.v](consistency.v) defines the conventional consistency relation (figure 1 in paper)
- [theories/cast_calculus/typing.v](typing.v) defines the typing rules for expressions.
We restrict our typing derivations so that they only treat meaningful types; the closed types (types with no free variables) (see [theories/prelude.v] for the formal definition of closedness).
- [theories/cast_calculus/contexts.v](contexts.v) defines general contexts (not evaluation contexts) together with their typing rules.
- [theories/cast_calculus/ctx_equiv.v](ctx_equiv.v) Defines contextual equivalence.

### Verifying the embedding from STLCmu into the cast calculus

- [theories/embedding/expressions.v] defines the embedding on expressions
- [theories/embedding/contexts.v] defines the embedding on contexts
- [theories/embedding/types.v] defines the embedding on types
- [theories/embedding/well_typedness.v] proves the preservation of well-typedness after embedding

### Verifying full abstraction claim

The file [theories/fae.v] proves full abstraction of the embedding.
Theorem `ctx_eq_preservation` proves preservation of equivalences, and `ctx_eq_reflection` proves reflection of equivalences.

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
The file `theories/fae.v` brings everything together.

## Credits
Lots of code has its origin in the following;
https://gitlab.mpi-sws.org/iris/examples/-/tree/master/theories/logrel/F_mu_ref_conc



curl make m4 gcc git
