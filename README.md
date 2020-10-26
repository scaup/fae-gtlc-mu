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

#### Laying out ground work

Alternative consistency relation (figure 9 in paper) on which the backtranslation for casts will be inductively defined.
- [theories/backtranslation/alternative_consistency.v](theories/backtranslation/alternative_consistency.v) definition relation
- [theories/backtranslation/implication_consistencies/proof.v](theories/backtranslation/implication_consistencies/proof.v) proves that the conventional relations implies the alternative one, as is claimed in the "Is this Well-Defined"-paragraph.

Definition of the static Universe type and the backtranslation on types.
- [theories/backtranslation/cast_help/universe.v](theories/backtranslation/cast_help/universe.v) defines the universe (equation 1 in paper)
- [theories/backtranslation/types.v](theories/backtranslation/types.v) defines the backtranslation on types (figure 6 and equation 1 in paper)

Static functions (and proofs of their well-typedness) that will be used later in the backtranslation for casts
- [theories/backtranslation/cast_help/embed.v](theories/backtranslation/cast_help/embed.v) defines embedding functions (figure 7 in paper)
- [theories/backtranslation/cast_help/extract.v](theories/backtranslation/cast_help/extract.v) defines extraction functions (figure 7 in paper)
- [theories/backtranslation/cast_help/identity.v](theories/backtranslation/cast_help/identity.v) defines identity function
- [theories/backtranslation/cast_help/factorize.v](theories/backtranslation/cast_help/factorize.v): defines factorization function
- [theories/backtranslation/cast_help/between.v](theories/backtranslation/cast_help/between.v): defines decomposition of casts between sum, product, recursive and arrow types

#### Bringing stuff together
- [theories/backtranslation/cast_help/general_def.v](theories/backtranslation/cast_help/general_def.v) brings the previously defined static functions together to define the backtranslation of a cast between two consistent types as a function by recursion on the alternative consistency relation (figure 9)
- [theories/backtranslation/expressions.v](theories/backtranslation/expressions.v): Defines the actual backtranslation on terms. Here we needed our proof of the fact that conventional consistency implies the alternative one.
- [theories/backtranslation/contexts.v](theories/backtranslation/contexts.v): Naturally extends the backtranslation to contexts.
- [theories/backtranslation/well_typedness.v](theories/backtranslation/well_typedness.v): proves well-typedness of backtranslation

### Defining logical relations from static to gradual (section 4.3.3)

- [theories/refinements/static_gradual/resources_left.v](theories/refinements/static_gradual/resources_left.v): setting up Iris resources for static side
- [theories/refinements/static_gradual/resources_right.v](theories/refinements/static_gradual/resources_right.v): setting up Iris resources for gradual side
- [theories/refinements/static_gradual/logical_relation.v](theories/refinements/static_gradual/logical_relation.v): defining logical relations (section 4.3.3 in paper)

### Proving specification for LR from static to gradual (section 4.3.2 and 4.3.4)

The file [theories/refinements/static_gradual/compat_easy.v](theories/refinements/static_gradual/compat_easy.v) proves the unexciting compatibility lemmas (fig 12 in the paper).

For the compatibility lemma between casts (lemma 4.7 in paper), we first define the (to-be-proven) proposition named `back_cast_ar` in [theories/refinements/static_gradual/compat_cast/defs.v](theories/refinements/static_gradual/compat_cast/defs.v).
The proposition `back_cast_ar` deviates slightly from lemma 4.7 in the paper, as it is more ergonomic to prove.

The file [theories/refinements/static_gradual/compat_cast/all.v](theories/refinements/static_gradual/compat_cast/all.v) actually proves proposition `back_cast_ar` by induction on the alternative consistency relation. 
The different inductive cases are proven in all the other files from the same directory: [between_rec.v](theories/refinements/static_gradual/compat_cast/between_rec.v), [prod_prod.v](theories/refinements/static_gradual/compat_cast/prod_prod.v), [sum_sum.v](theories/refinements/static_gradual/compat_cast/sum_sum.v), [arrow_arrow.v](theories/refinements/static_gradual/compat_cast/arrow_arrow.v), [identity.v](theories/refinements/static_gradual/compat_cast/identity.v), [tau_star.v](theories/refinements/static_gradual/compat_cast/tau_star.v), [ground_star.v](theories/refinements/static_gradual/compat_cast/ground_star.v), [tau_star.v](theories/refinements/static_gradual/compat_cast/tau_star.v), [star_tau.v](theories/refinements/static_gradual/compat_cast/star_tau.v), and [star_ground.v](theories/refinements/static_gradual/compat_cast/star_ground.v).
Afterwards, the actual compatibility for casts (lemma 4.7) is proven (`bin_log_related_back_cast`) out of `back_cast_ar`.

The file [theories/refinements/static_gradual/rel_ref_specs.v][theories/refinements/static_gradual/rel_ref_specs.v] proves that gradual contexts are related to their backtranslation and that static terms are related to their embeddings (lemma 4.2 in paper); to do this, it basically applies all the aforementioned compatibility lemmas.
In [theories/refinements/static_gradual/adequacy.v](theories/refinements/static_gradual/adequacy.v), adequacy of the logical relations are proven (lemma 4.3).

### Defining logical relations from gradual to static (mostly analogous and not in the paper)

- [theories/refinements/gradual_static/resources_left.v](theories/refinements/gradual_static/resources_left.v): setting up Iris resources for gradual side
- [theories/refinements/gradual_static/resources_right.v](theories/refinements/gradual_static/resources_right.v): setting up Iris resources for static side
- [theories/refinements/gradual_static/logical_relation.v](theories/refinements/gradual_static/logical_relation.v) defining logical relations

### Proving specification for LR from gradual to static (mostly analogous and mostly absent in paper)

The file [theories/refinements/gradual_static/compat_easy.v](theories/refinements/gradual_static/compat_easy.v) proves the unexciting compatibility lemmas (not in paper).

For the compatibility lemma between casts (not in paper), we first define the (to-be-proven) proposition named `back_cast_ar` in [theories/refinements/gradual_static/compat_cast/defs.v](theories/refinements/gradual_static/compat_cast/defs.v).
The proposition `back_cast_ar` deviates slightly from the compatibility lemma on casts, as it is more ergonomic to prove.

The file [theories/refinements/gradual_static/compat_cast/all.v](theories/refinements/gradual_static/compat_cast/all.v) actually proves proposition `back_cast_ar` by induction on the alternative consistency relation. 
The different inductive cases are proven in all the other files from the same directory: [between_rec.v](theories/refinements/gradual_static/compat_cast/between_rec.v), [prod_prod.v](theories/refinements/gradual_static/compat_cast/prod_prod.v), [sum_sum.v](theories/refinements/gradual_static/compat_cast/sum_sum.v), [arrow_arrow.v](theories/refinements/gradual_static/compat_cast/arrow_arrow.v), [identity.v](theories/refinements/gradual_static/compat_cast/identity.v), [tau_star.v](theories/refinements/gradual_static/compat_cast/tau_star.v), [ground_star.v](theories/refinements/gradual_static/compat_cast/ground_star.v), [tau_star.v](theories/refinements/gradual_static/compat_cast/tau_star.v), [star_tau.v](theories/refinements/gradual_static/compat_cast/star_tau.v), and [star_ground.v](theories/refinements/gradual_static/compat_cast/star_ground.v).
Afterwards, the actual compatibility for casts is proven (`bin_log_related_back_cast`) out of `back_cast_ar`.

The file [theories/refinements/gradual_static/rel_ref_specs.v][theories/refinements/gradual_static/rel_ref_specs.v] proves that gradual contexts are related to their backtranslation and that static terms are related to their embeddings (lemma 4.4 in paper); to do this, it basically applies all the aforementioned compatibility lemmas.
In [theories/refinements/gradual_static/adequacy.v](theories/refinements/gradual_static/adequacy.v), adequacy of the logical relations are proven (lemma 4.5).

### Bringing stuff together in [theories/fae.v](theories/fae.v)

Both directions of theorem 4.1 from the paper are proven there; 
left to right is proven by `static_ctx_refines_gradual` and right to left by `gradual_ctx_refines_static`.
Finally, all is brought together to prove full abstraction.

## Credits

Lots of code has its origin in the following;
https://gitlab.mpi-sws.org/iris/examples/-/tree/master/theories/logrel/F_mu_ref_conc
