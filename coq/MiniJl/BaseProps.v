(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(*    MiniJl:
        Decidable, Tag-Based Semantic Subtyping 
        for Nominal Types, Pairs, and Unions.  *)

(** * MiniJl: Simple Propositions *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

Add LoadPath "../..". (* root directory of the repo *)

Require Import MiniJl.Aux.Identifier.
Require Import MiniJl.MiniJl.BaseDefs.

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.


(* ################################################################# *)
(** ** Decidability *)
(* ################################################################# *)

(* ================================================================= *)
(** *** Value Type *)
(* ================================================================= *)

(** [value_type t] is decidable *)
Theorem value_type__dcdbl : forall (t : ty),
    Decidable.decidable (value_type t).
Proof.
  induction t;
    try solve [right; intros Hcontra; inversion Hcontra].
  - (* CName *)
    left; constructor.
  - (* Pair *)
    destruct IHt1 as [IHt1 | IHt1]; destruct IHt2 as [IHt2 | IHt2];
      try solve [right; intros Hcontra; inversion Hcontra; subst;
                 contradiction].
    left; constructor; assumption.
Qed.

(* ================================================================= *)
(** *** CName *)
(* ================================================================= *)

(** Equality of names [cn1 = cn2] is decidable *)
Lemma cname_eq__decidable : forall (n1 n2 : cname),
    Decidable.decidable (n1 = n2).
Proof.
  intros n1 n2; destruct n1; destruct n2;
    (left; reflexivity) || 
    (right; intros H; inversion H).
Qed.

(* ================================================================= *)
(** *** AName *)
(* ================================================================= *)

(** Equality of names [an1 = an2] is decidable *)
Lemma aname_eq__decidable : forall (n1 n2 : aname),
    Decidable.decidable (n1 = n2).
Proof.
  intros n1 n2; destruct n1; destruct n2;
    (left; reflexivity) || 
    (right; intros H; inversion H).
Qed.

(* ################################################################# *)
(** ** Normal Form irregardless Subtyping *)
(* ################################################################# *)

Open Scope btjnf_scope.

(* ================================================================= *)
(** *** Properties of InNF *)
(* ================================================================= *)

(** Value type is normal form. *)
Lemma valty_in_nf : forall (v : ty),
    value_type v ->
    InNF(v).
Proof.
  intros v Hval; induction Hval; repeat constructor; assumption.
Qed.

(** If union is in normal form, its components also are. *)
Lemma union_in_nf__components_in_nf : forall (t1 t2 : ty),
    InNF(TUnion t1 t2) ->
    InNF(t1) /\ InNF(t2).
Proof.
  intros t1 t2 Hnf. inversion Hnf; subst.
  inversion H. tauto.
Qed.


(* ================================================================= *)
(** *** Properties of MkNF *)
(* ================================================================= *)

(* ----------------------------------------------------------------- *)
(** **** Aux *)
(* ----------------------------------------------------------------- *)

Lemma unite_pairs_t_union : forall (t t1 t2 : ty),
    ~ (exists ta tb, t = TUnion ta tb) ->
    unite_pairs t (TUnion t1 t2) = TUnion (unite_pairs t t1) (unite_pairs t t2).
Proof.
  intros t t1 t2 Hcontra.
  destruct t; try solve [simpl; reflexivity].
  assert (H: exists ta tb, TUnion t3 t4 = TUnion ta tb).
  { exists t3, t4; reflexivity. }
  contradiction.
Qed.

(* Helper for [unite_pairs_t_union] *)
Ltac resolve_not_union :=
  intros [tx [ty Hcontra]]; inversion Hcontra.

Ltac resolve_not_value_type :=
  try solve [
        match goal with
          [H: value_type (TUnion _ _) |-_] => inversion H
        | [H: value_type (TAName _) |- _] => inversion H
        end
      ].

Lemma unite_pairs_union_t : forall (t1 t2 t' : ty),
    unite_pairs (TUnion t1 t2) t' = TUnion (unite_pairs t1 t') (unite_pairs t2 t').
Proof.
  intros t1 t2 t'.
  destruct t'; try solve [simpl; reflexivity].
Qed.

(* DEP: unite_pairs_t_union, unite_pairs_union_t *)
Lemma unite_pairs__preserves_nf : forall (t1 t2 : ty),
    InNF(t1) ->
    InNF(t2) ->
    InNF(unite_pairs t1 t2).
Proof.
  intros ta tb Hnfa. generalize dependent tb.
  induction Hnfa; intros tb; intros Hnfb; induction Hnfb.
  - (* Value, Value *)
    destruct v; destruct v0; simpl; resolve_not_value_type.
    + repeat constructor; assumption.
    + inversion H0; subst. repeat constructor; try assumption.
    + inversion H; subst.  repeat constructor; try assumption.
    + inversion H; inversion H0; subst. repeat constructor; try assumption.
  - (* Value, Union *)
    destruct v; subst; resolve_not_value_type.
    + rewrite unite_pairs_t_union; try resolve_not_union.
      apply NF_Union; try assumption.
    + rewrite unite_pairs_t_union; try resolve_not_union.
      apply NF_Union; assumption.
  - (* Union, Value *)
    rewrite unite_pairs_union_t.
    apply NF_Union; [apply IHHnfa1 | apply IHHnfa2];
      apply NF_Value; assumption.
  - (* Union, Union *)
    simpl. apply NF_Union;
    [apply IHHnfa1 | apply IHHnfa2]; apply NF_Union; assumption.
Qed.

Lemma unite_pairs_of_valtys : forall (v1 v2 : ty),
    value_type v1 ->
    value_type v2 ->
    unite_pairs v1 v2 = TPair v1 v2.
Proof.
  intros v1 v2 Hval1; induction Hval1;
    intros Hval2; induction Hval2;
      try solve [simpl; reflexivity].
Qed.

(* ----------------------------------------------------------------- *)
(** **** Main Properties *)
(* ----------------------------------------------------------------- *)

(** [MkNF] returns normal form. *)
(* DEP: unite_pairs__preserves_nf *)
Theorem mk_nf__in_nf : forall (t : ty),
    InNF(MkNF(t)).
Proof.
  induction t.
  - (* CName *)
    simpl. repeat constructor.
  - (* AName *)
    destruct a; simpl; repeat apply NF_Union; repeat constructor.
  - (* Pair *)
    simpl. apply unite_pairs__preserves_nf; assumption.
  - (* Union *)
    simpl. apply NF_Union; assumption.
Qed.

(* DEP: unite_pairs_of_valtys *)
Lemma mk_nf_valty__equal : forall (v : ty),
    value_type v ->
    MkNF(v) = v.
Proof.
  intros v Hval; induction Hval.
  - (* CName *)
    simpl; reflexivity.
  - (* Pair *)
    simpl. rewrite IHHval1. rewrite IHHval2.
    rewrite unite_pairs_of_valtys; try assumption.
    reflexivity.
Qed.

(* DEP: mk_nf_valty__equal *)
Lemma mk_nf_nf__equal : forall (t : ty),
    InNF(t) ->
    MkNF(t) = t.
Proof.
  intros t Hnf; induction Hnf.
  - (* Value *)
    apply mk_nf_valty__equal; assumption.
  - (* Union *)
    simpl. rewrite IHHnf1. rewrite IHHnf2. reflexivity.
Qed.

(* DEP: mk_nf_of_nf__equal, mk_nf__in_nf *)
Lemma mk_nf__idempotent : forall (t : ty),
    MkNF( MkNF(t) ) = MkNF(t).
Proof.
  intros t. apply mk_nf_nf__equal.
  apply mk_nf__in_nf.
Qed.


(* ################################################################# *)
(** ** Declarative Subtyping *)
(* ################################################################# *)

Close Scope btjr_scope.
Open  Scope btj_scope.

Lemma union_sub_d__components_sub_d : forall (t1 t2 t' : ty),
    |- TUnion t1 t2 << t' ->
    |- t1 << t' /\ |- t2 << t'.
Proof.
  intros t1 t2 t' H. remember (TUnion t1 t2) as t eqn:Heq.
  induction H; try solve [inversion Heq].
  - (* Refl *)
    subst; split; constructor.
  - (* Trans *)
    specialize (IHsub_d1 Heq); destruct IHsub_d1 as [Hsub1 Hsub2].
    split; apply SD_Trans with t3; assumption.
  - (* UnionL *)
    inversion Heq; subst. split; assumption.
  - (* UnionR1 *)
    inversion Heq; subst. split; apply union_right_1.
    apply SD_UnionR1. apply SD_UnionR2.
  - (* UnionR2 *)
    inversion Heq; subst. split; apply union_right_2.
    apply SD_UnionR1. apply SD_UnionR2.
Qed.


(* ################################################################# *)
(** ** Reductive Subtyping *)
(* ################################################################# *)

Close Scope btj_scope.
Open  Scope btjr_scope.

(* ================================================================= *)
(** *** Reflexivity *)
(* ================================================================= *)

Lemma sub_r__rflxv : forall (t : ty),
    |- t << t.
Proof.
  induction t; try solve [constructor; assumption].
  - (* AName *)
    destruct a; apply SR_NormalForm;
      simpl; repeat constructor.
  - (* Union *)
    constructor;
      [apply SR_UnionR1 | apply SR_UnionR2]; assumption.
Qed.

(* ================================================================= *)
(** *** Relation to Value types *)
(* ================================================================= *)

(* DEP: mk_nf_nf__equal *)
Lemma sub_r_value_types__equal : forall (v1 v2 : ty),
    |- v1 << v2 ->
    value_type v1 ->
    value_type v2 ->
    v1 = v2.
Proof.
  intros v1 v2 Hsub; induction Hsub; intros Hval1 Hval2;
    try solve [reflexivity | inversion Hval1 | inversion Hval2].
  - (* Pair *)
    inversion Hval1; inversion Hval2; subst.
    rewrite IHHsub1; try assumption;
      rewrite IHHsub2; try assumption.
    reflexivity.
  - (* NF *)
    rewrite mk_nf_nf__equal in IHHsub.
    apply IHHsub; assumption. apply NF_Value; assumption.
Qed.
