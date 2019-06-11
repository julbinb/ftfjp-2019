(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(*    FullAtomicJl:
        Decidable, Tag-Based Semantic Subtyping 
        for Nominal Types, Pairs, and Unions.  *)

(** * FullAtomicJl: Propositions about Matching Relation *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

Add LoadPath "../..". (* root directory of the repo *)

Require Import Mechanization.Aux.Identifier.

Require Import Mechanization.FullAtomicJl.BaseDefs.
Require Import Mechanization.FullAtomicJl.BaseProps.

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
    try solve [inversion Hval2 | reflexivity].
  (* Pair *)
  inversion Hval2; subst.
  apply IHHm1 in H1. apply IHHm2 in H2.
  subst; reflexivity.
Qed.

Lemma matching_valty__exists : forall (t : ty),
    exists (v : ty),
      value_type v  /\  |- v <$ t.
Proof.
  induction t.
  - (* CName *)
    exists (TCName c); repeat constructor.
  - (* AName *)
    exists (TExt a); repeat constructor.
  - (* Pair *)
    destruct IHt1 as [v1 [Hv1 Hm1]]; destruct IHt2 as [v2 [Hv2 Hm2]].
    exists (TPair v1 v2); auto.
  - (* Union *)
    destruct IHt1 as [v1 [Hv1 Hm1]].
    exists v1; auto.
  - (* Ext *)
    exists (TExt a); repeat constructor.
Qed.

(* DEP: matching_valty__exists *)
Lemma matching_valpair__exists : forall (t1 t2 : ty),
    exists (v1 v2 : ty),
      value_type (TPair v1 v2)  /\  |- TPair v1 v2 <$ TPair t1 t2.
Proof.
  intros t1 t2.
  destruct (matching_valty__exists t1) as [v1 [Hv1 Hm1]].
  destruct (matching_valty__exists t2) as [v2 [Hv2 Hm2]].
  exists v1, v2. split;
  constructor; assumption.
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
    + (* Ext *)
      right; intros Hcontra; inversion Hcontra.
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
    + (* Ext *)
      right; intros Hcontra; inversion Hcontra.
  - (* Union *)
    right; intros Hcontra.
    apply match_ty__value_type in Hcontra.
    inversion Hcontra.
  - (* Ext *)
    induction t;
      try solve [right; intros Hcontra; inversion Hcontra].
    + (* AName *)
      destruct a; destruct a0;
        try solve [left; constructor].
      right; intros Hcontra; inversion Hcontra.
    + (* Union *)
      destruct IHt1 as [IH1 | IH1];
        destruct IHt2 as [IH2 | IH2];
        try solve [
              left; apply MT_Union1; assumption
            | left; apply MT_Union2; assumption ].
      right; intros Hcontra.
      inversion Hcontra; contradiction.
    + (* Ext *)
      destruct (aname_eq__decidable a a0).
      left; subst; constructor.
      right; intros Hcontra; inversion Hcontra; contradiction.
Qed.
