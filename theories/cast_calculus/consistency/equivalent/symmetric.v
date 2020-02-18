From Autosubst Require Export Autosubst.
From fae_gtlc_mu Require Import prelude.
From fae_gtlc_mu.cast_calculus Require Import types consistency.standard consistency.structural.definition.

 Definition flip (A : Assumption) : Assumption :=
  match A with
  | NoStars τl τr Pl Pr => NoStars τr τl Pr Pl
  | StarOnLeft τr => StarOnRight τr
  | StarOnRight τl => StarOnLeft τl
  end.

Lemma flipflip a : flip (flip a) = a.
  by destruct a.
Qed.

Lemma flipflipmap l : map flip (map flip l) = l.
  induction l.
  by simpl.
  simpl. by rewrite flipflip IHl.
Qed.

Lemma map_update (f : Assumption -> Assumption) (l : list Assumption) i a :
  map f (update l i a) = update (map f l) i (f a).
Proof.
  unfold update.
  apply list_alter_fmap. induction l. constructor. constructor. auto. auto.
Qed.

Lemma map_flip_update (l : list Assumption) i a :
  map flip (update l i a) = update (map flip l) i (flip a).
Proof.
  unfold update.
  apply list_alter_fmap. induction l. constructor. constructor. auto. auto.
Qed.

Lemma cons_struct_symmetric (A : list Assumption) (τ τ' : type) (P : cons_struct A τ τ') :
  cons_struct (map flip A) τ' τ.
Proof.
  induction P; try by constructor.
  - apply consStarTau with (τG := τG); by (done || rewrite map_length).
  - apply consTauStar with (τG := τG); by (done || rewrite map_length).
  - apply consTRecTRecNoStars with (Pl := Pr) (Pr := Pl).
    by rewrite map_cons in IHP.
  - apply (consStarTVar (map flip A) i τr τl Pr Pl).
    by rewrite list_lookup_fmap e.
    simpl in IHP.
    by rewrite map_update in IHP.
  - apply (consTVarStar (map flip A) i τr τl Pr Pl).
    by rewrite list_lookup_fmap e.
    simpl in IHP.
    by rewrite map_update in IHP.
  - eapply (consTVars (map flip A) i _ _ Pr Pl). by rewrite list_lookup_fmap e.
  - apply consStarTVarUse with (τr := τl).
    by rewrite list_lookup_fmap e.
  - apply consTVarStarUse with (τl := τr).
    by rewrite list_lookup_fmap e.
Qed.
