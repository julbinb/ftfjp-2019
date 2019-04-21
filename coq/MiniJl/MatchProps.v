(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(*    MiniJl:
        Decidable, Tag-Based Semantic Subtyping 
        for Nominal Types, Pairs, and Unions.  *)

(** * MiniJl: Propositions about Matching Relation *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

Add LoadPath "../..". (* root directory of the repo *)

Require Import MiniJl.Aux.Identifier.

Require Import MiniJl.MiniJl.BaseDefs.
Require Import MiniJl.MiniJl.BaseProps.

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.

Open  Scope btjm_scope.

(* ################################################################# *)
(** ** Basic Properties *)
(* ################################################################# *)

(** Only a _value_ type _matches a type. *)
Lemma match_ty__value_type : forall (v t : ty),
    |- v <$ t ->
    value_type v.
Proof.
  intros v t H; induction H;
    try solve [assumption | constructor; assumption].
Qed.

(** Any value type matches itself. *)
Lemma match_valty__rflxv : forall (v : ty),
    value_type v ->
    |- v <$ v.
Proof.
  intros v Hval; induction Hval; constructor; assumption.
Qed.

(** A value type matches only an eqivalent value type. *)
Lemma valty_match_valty__equal : forall (v1 v2 : ty),
    |- v1 <$ v2 ->
    value_type v2 ->
    v1 = v2.
Proof.
  intros v1 v2 Hm; induction Hm; intros Hval2;
    try solve [inversion Hval2].
  - (* CName, CName *)
    reflexivity.
  - (* Pair *)
    inversion Hval2; subst.
    apply IHHm1 in H1. apply IHHm2 in H2.
    subst; reflexivity.
Qed.


(* ################################################################# *)
(** ** Decidability *)
(* ################################################################# *)

(* DEP: cname_eq__decidable, valty_match_valty__equal,
        match_ty__value_type *)
Theorem match_ty__dcdbl : forall (v t : ty),
    Decidable.decidable (|- v <$ t).
Proof.
  intros v; induction v; intros t.
  - (* CName *)
    assert (Hval1: value_type (TCName c)) by constructor.
    induction t.
    + (* CName *)
      destruct (cname_eq__decidable c c0).
      * subst; left; constructor.
      * right; intros Hcontra.
        assert (Hval2: value_type (TCName c0)) by constructor.
        pose proof (valty_match_valty__equal _ _ Hcontra Hval2) as Heq.
        inversion Heq; contradiction.
    + (* AName *)
      destruct c; destruct a;
        try solve [
              left; constructor
            | right; intros Hcontra; inversion Hcontra ].
    + (* Pair *)
      right; intros Hcontra; inversion Hcontra.
    + (* Union *)
      destruct IHt1 as [IH1 | IH1]; destruct IHt2 as [IH2 | IH2];
        try solve [ left; apply MT_Union1; assumption
                  | left; apply MT_Union2; assumption ].
      right; intros Hcontra.
      inversion Hcontra; subst; contradiction.
  - (* AName *)
    right; intros Hcontra.
    apply match_ty__value_type in Hcontra; inversion Hcontra.
  - (* Pair *)
    induction t.
    + (* CName *)
      right; intros Hcontra; inversion Hcontra.
    + (* AName *)
      right; intros Hcontra; inversion Hcontra.
    + (* Pair *)
      destruct (IHv1 t1) as [IH1 | IH1];
        destruct (IHv2 t2) as [IH2 | IH2];
        try solve [right; intros Hcontra;
                   inversion Hcontra; subst; contradiction].
      left; constructor; assumption.
    + (* Union *)
      destruct IHt1 as [IH1 | IH1];
        destruct IHt2 as [IH2 | IH2];
        try solve [
              left; apply MT_Union1; assumption
            | left; apply MT_Union2; assumption ].
      right; intros Hcontra.
      inversion Hcontra; contradiction.
  - (* Union *)
    right; intros Hcontra.
    apply match_ty__value_type in Hcontra.
    inversion Hcontra.
Qed.
