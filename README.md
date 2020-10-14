# the embedding of STLCmu into GTLCmu is fully abstract (Coq/Iris proof)

This repo contains a Coq/Iris proof of the fact that the embedding of STLCmu (the simply typed lambda calculus with equirecursive types) into GTLCmu (its gradualization) is fully abstract.
It accompanies the paper  "Fully abstract from Static to Gradual".

## How to compile Coq code

### Requirements

- Coq: 8.11.1
- Coq libraries
  * stdpp: dev.2020-04-03.1.eeef6250
  * IRIS: dev.2020-04-07.7.64bed0ca
  * coq-autosubs: dev.coq86

### Getting started quickly with opam

#### Free disk space

Please note that fetching and compiling the requirements by following the instruction described below calls for roughly 1.4GB of free disk space.

#### Fetching and compiling requirements

An easy way to get the correct version of Coq and the required libraries is by using opam.

Get [opam](http://opam.ocaml.org/doc/Install.html), by fetching and running the install script.
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
#### Some optional sanity checks
Verify that installation went OK
```
$ opam list # output should list the required packages with the right versions
$ which coqc # verify that coqc is in your path, if not, run "eval $(opam env)"
$ coqc --version # should return 8.11.1, and "compiled on" should be realistic
$ coqc --config # check the COQLIB=~/.opam/fae/lib/coq/ variable
$ ls ~/.opam/fae/lib/coq/user-contrib # should return the Autosubst, iris, Ltac2 and stdpp directories
```
#### Compiling the fae proof

Compile by running `make` in the root of this folder.
```
$ make
```
Run `make clean` in the root of this folder to remove all but the source files.

## Verifying the full abstraction claim

This section describes the files necessary to go through in order to verify that full abstraction is indeed proven for the embedding from STLCmu to GTLCmu.

### Verifying definition of the simply typed lambda calculus with iso-recursive types

- [theories/stlc_mu/lang.v](theories/stlc_mu/lang.v) starts by defining the expressions and values;
for this we use De Bruijn indices, utilizing [Autosubst](https://www.ps.uni-saarland.de/autosubst/doc/manual.pdf) to do so (detailed knowledge is not required).
Afterwards, it defines evaluation contexts (of depth 1) and head step reductions.
The final language is defined using the `EctxiLanguage` construct from the Iris library; essentially, it naturally defines the general evaluation contexts and the total reduction relation.
Lastly, we define the `Halts` predicative for expressions.
- [theories/stlc_mu/types.v](theories/stlc_mu/types.v) defines the static types (again using Autosubst).
- [theories/stlc_mu/typing.v](theories/stlc_mu/typing.v) defines the typing rules for expressions.
We restrict our typing derivations so that they only treat meaningful types; the closed types (types with no free variables) (see [theories/prelude.v](theories/prelude.v) for the formal definition of closedness).
- [theories/stlc_mu/contexts.v](theories/stlc_mu/contexts.v) defines general contexts (not evaluation contexts) together with their typing rules.
- [theories/stlc_mu/ctx_equiv.v](theories/stlc_mu/ctx_equiv.v) defines contextual equivalence.

### Verifying definition of the cast calculus of GTLCmu

- [theories/cast_calculus/types.v](theories/cast_calculus/types.v) defines the gradual types, ground types, the shape operator (S in figure 2 of paper) and type `ICP` to encode inert pairs (two function types or a ground and unknown type) which is used in [theories/cast_calculus/lang.v](theories/cast_calculus/lang.v) to define which expressions are values.
- [theories/cast_calculus/types_notations.v](theories/cast_calculus/types_notations.v) defines some handy notations for types.
- [theories/cast_calculus/lang.v](theories/cast_calculus/lang.v) defines expressions, values, evaluation contexts, head reductions, total reduction, and a `Halts` predicate on expressions.
- [theories/cast_calculus/consistency.v](theories/cast_calculus/consistency.v) defines the conventional consistency relation (figure 1 in paper)
- [theories/cast_calculus/typing.v](theories/cast_calculus/typing.v) defines the typing rules for expressions.
We restrict our typing derivations so that they only treat meaningful types; the closed types (types with no free variables) (see [theories/prelude.v] for the formal definition of closedness).
- [theories/cast_calculus/contexts.v](theories/cast_calculus/contexts.v) defines general contexts (not evaluation contexts) together with their typing rules.
- [theories/cast_calculus/ctx_equiv.v](theories/cast_calculus/ctx_equiv.v) defines contextual equivalence.

### Verifying the embedding from STLCmu into the cast calculus

- [theories/embedding/expressions.v](theories/embedding/expressions.v) defines the embedding on expressions
- [theories/embedding/contexts.v](theories/embedding/contexts.v) defines the embedding on contexts
- [theories/embedding/types.v](theories/embedding/types.v) defines the embedding on types
- [theories/embedding/well_typedness.v](theories/embedding/well_typedness.v) proves the preservation of well-typedness after embedding

### Verifying full abstraction claim

The file [theories/fae.v](theories/fae.v) proves full abstraction of the embedding.
Theorem `ctx_eq_preservation` proves preservation of equivalences, and `ctx_eq_reflection` proves reflection of equivalences.

## Proof structure (where's what?)

Cool, so you're actually interested in the proof itself!
This section describes some of the more interesting files that make up the proof, referring to the paper where possible;
for a complete listing of all files, one can refer to the commented [_CoqProject](_CoqProject) file.

### Defining backtranslation (section 4.2 in paper)

- [theories/backtranslation/alternative_consistency.v](theories/backtranslation/alternative_consistency.v) defines the alternative consistency relation as in figure 9 of paper
- [theories/backtranslation/implication_consistencies/proof.v](theories/backtranslation/implication_consistencies/proof.v) proves that the conventional relations implies the alternative one, as is claimed in the "Is this Well-Defined"-paragraph
- [theories/backtranslation/cast_help/universe.v](theories/backtranslation/cast_help/universe.v) defines the universe (equation 1 in paper)
- [theories/backtranslation/types.v](theories/backtranslation/types.v) defines the backtranslation on types (figure 6 and equation 1 in paper)
- [theories/backtranslation/cast_help/embed.v](theories/backtranslation/cast_help/embed.v) defines backtranslation of casts from ground to unknown (figure 7 in paper)
- [theories/backtranslation/cast_help/extract.v](theories/backtranslation/cast_help/extract.v) defines backtranslation of casts from unknown to ground (figure 7 in paper)
- [theories/backtranslation/cast_help/extract.v](theories/backtranslation/cast_help/extract.v) defines backtranslation of casts from unknown to ground (figure 7 in paper)
- [theories/backtranslation/cast_help/factorize.v](theories/backtranslation/cast_help/factorize.v): factorizing upcasts and downcasts (figure 9)
- [theories/backtranslation/cast_help/between.v](theories/backtranslation/cast_help/between.v): casts between sum, product, recursive and arrow types
- [theories/backtranslation/cast_help/general_def.v](theories/backtranslation/cast_help/general_def.v) brings it all together (figure 9)

- [theories/backtranslation/expressions.v](theories/backtranslation/expressions.v): actual backtranslation on terms
- [theories/backtranslation/contexts.v](theories/backtranslation/contexts.v): on contexts
- [theories/backtranslation/well_typedness.v](theories/backtranslation/well_typedness.v): proves well-typedness of backtranslation

### Defining logical relations from static to gradual (section 4.3.3)

- [theories/refinements/static_gradual/resources_left.v](theories/refinements/static_gradual/resources_left.v): setting up Iris resources for static side
- [theories/refinements/static_gradual/resources_right.v](theories/refinements/static_gradual/resources_right.v): setting up Iris resources for gradual side
- [theories/refinements/static_gradual/logical_relation.v](theories/refinements/static_gradual/logical_relation.v): defining logical relations (section 4.3.3 in paper)

### Proving specification for LR from static to gradual (section 4.3.2 and 4.3.4)

- [theories/refinements/static_gradual/compat_easy.v](theories/refinements/static_gradual/compat_easy.v) proves the unexciting lemmas (fig 12 in the paper)
- [theories/refinements/static_gradual/compat_cast/defs.v](theories/refinements/static_gradual/compat_cast/defs.v) defines the generalized compatibility lemma for casts (lemma 4.7)
- [theories/refinements/static_gradual/compat_cast/all.v](theories/refinements/static_gradual/compat_cast/all.v) proves the compatibility lemma on casts; it brings together the different cases defined in the same folder
- [theories/refinements/static_gradual/rel_ref_specs.v][theories/refinements/static_gradual/rel_ref_specs.v] proves that gradual contexts are related to their backtranslation and that static terms are related to their embeddings (lemma 4.2 in paper)
- [theories/refinements/static_gradual/adequacy.v](theories/refinements/static_gradual/adequacy.v) proves adequacy of logical relations (lemma 4.3)

### Defining logical relations from gradual to static (mostly analogous and not in the paper)

- [theories/refinements/gradual_static/resources_left.v](theories/refinements/gradual_static/resources_left.v): setting up Iris resources for gradual side
- [theories/refinements/gradual_static/resources_right.v](theories/refinements/gradual_static/resources_right.v): setting up Iris resources for static side
- [theories/refinements/gradual_static/logical_relation.v](theories/refinements/gradual_static/logical_relation.v) defining logical relations

### Proving specification for LR from gradual to static (mostly analogous and mostly absent in paper)

- [theories/refinements/gradual_static/compat_easy.v](theories/refinements/gradual_static/compat_easy.v) proves the unexciting lemmas (not in paper)
- [theories/refinements/gradual_static/compat_cast/defs.v](theories/refinements/gradual_static/compat_cast/defs.v) defines the generalized compatibility lemma for casts (not in paper)
- [theories/refinements/gradual_static/compat_cast/all.v](theories/refinements/gradual_static/compat_cast/all.v) proves the compatibility lemma on casts; it brings together the different cases defined in the same folder
- [theories/refinements/gradual_static/rel_ref_specs.v][theories/refinements/gradual_static/rel_ref_specs.v] proves that static contexts are related to their backtranslation and that gradual terms are related to their embeddings (lemma 4.4 in paper)
- [theories/refinements/gradual_static/adequacy.v](theories/refinements/static_static/adequacy.v) proves adequacy of logical relations (lemma 4.5)

### Bringing stuff together in [theories/fae.v](theories/fae.v)

Both directions of theorem 4.1 from the paper are proven there.

## Credits

Lots of code has its origin in the following;
https://gitlab.mpi-sws.org/iris/examples/-/tree/master/theories/logrel/F_mu_ref_conc
