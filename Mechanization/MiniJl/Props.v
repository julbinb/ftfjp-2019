(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(*    MiniJl:
        Decidable, Tag-Based Semantic Subtyping 
        for Nominal Types, Pairs, and Unions.  *)

(** * MiniJl: Main Propositions *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

Add LoadPath "../..". (* root directory of the repo *)

Require Import Mechanization.Aux.Identifier.

Require Import Mechanization.MiniJl.BaseDefs.
Require Import Mechanization.MiniJl.BaseProps.
Require Import Mechanization.MiniJl.MatchProps.
Require Import Mechanization.MiniJl.DeclSubProps.
Require Import Mechanization.MiniJl.RedSubProps.

Require Import Mechanization.Aux.BasicTactics.

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.

Open  Scope btjm_scope.

(* ################################################################# *)
(** ** On ValueType *)
(* ################################################################# *)

(** [value_type t] is decidable *)
Theorem value_type__decidable : forall (t : ty),
    Decidable.decidable (value_type t).
Proof.
  apply value_type__dcdbl.
Qed.


(* ################################################################# *)
(** ** On Matching *)
(* ################################################################# *)

(** Any value type matches itself. *)
Lemma match_valty__reflexive : forall (v : ty),
    value_type v ->
    |- v <$ v.
Proof.
  apply match_valty__rflxv.
Qed.

(** A value type matches only an eqivalent value type. *)
Lemma valty_match_valty__equal' : forall (v1 v2 : ty),
    |- v1 <$ v2 ->
    value_type v2 ->
    v1 = v2.
Proof.
  apply valty_match_valty__equal.
Qed.

(** [v <$ t] is decidable. *)
Theorem match_ty__decidable : forall (v t : ty),
    Decidable.decidable (|- v <$ t).
Proof.
  apply match_ty__dcdbl.
Qed.


(* ################################################################# *)
(** ** On Declarative Subtyping *)
(* ################################################################# *)

Close Scope btjr_scope.
Open  Scope btj_scope.

(* ================================================================= *)
(** *** Relation to Matching *)
(* ================================================================= *)

Theorem match_ty__sub_d_sound' : forall (v t : ty),
    |- v <$ t ->
    |- v << t.
Proof.
  apply match_ty__sub_d_sound.
Qed.

Theorem match_valty__sub_d_complete' : forall (v t : ty),
    |- v << t ->
    value_type v ->
    |- v <$ t.
Proof.
  apply match_valty__sub_d_complete.
Qed.

(* ================================================================= *)
(** *** Semantic Correctness *)
(* ================================================================= *)

(* ----------------------------------------------------------------- *)
(** **** Soundness *)
(* ----------------------------------------------------------------- *)

(** Declarative subtyping implies semantic: 
    [t1 << t2  ->  [t1] <= [t2]]. *)
(* DEP: match_valty__transitive_on_sub_d *)
Theorem sub_d__semantic_sound : forall (t1 t2 : ty),
    |- t1 << t2 ->
    ||- [t1] <= [t2].
Proof.
  intros t1 t2 Hsub. unfold sem_sub.
  apply match_valty__transitive_on_sub_d; assumption.
Qed.

(* ----------------------------------------------------------------- *)
(** **** Completeness *)
(* ----------------------------------------------------------------- *)

(** Semantic subtyping implies declarative:
    [[t1] <= [t2]  ->  t1 << t2]. *)
(* DEP: nf_exists, nf_sem_sub__sub_d, 
        match_valty__sub_d_complete, match_ty__sub_d_sound *)
Theorem sub_d__semantic_complete : forall (t1 t2 : ty),
    ||- [t1] <= [t2] ->
    |- t1 << t2.
Proof.
  intros t1 t2 Hsem.
  (* exists nt1 = NF(t1) *)
  pose proof (nf_exists t1) as [tn1 [Hnf1 [Hsub1 Hsub2]]].
  (* t1 << tn1 << t2 *)
  apply SD_Trans with tn1. assumption.
  apply nf_sem_sub__sub_d. assumption.
  (* [tn1] <= [t2] *)
  unfold sem_sub in *. intros v Hv Hm1.
  apply Hsem. assumption.
  apply match_valty__sub_d_complete; try assumption.
  apply SD_Trans with tn1; try assumption.
  apply match_ty__sub_d_sound; assumption.
Qed.


(* ################################################################# *)
(** ** On Reductive Subtyping *)
(* ################################################################# *)

Close Scope btj_scope.
Open  Scope btjr_scope.

(* ================================================================= *)
(** *** Relation to Matching *)
(* ================================================================= *)

Theorem match_ty__sub_r_sound' : forall (v t : ty),
    |- v <$ t ->
    |- v << t.
Proof.
  apply match_ty__sub_r_sound.
Qed.

Theorem match_valty__sub_r_complete' : forall (v t : ty),
    |- v << t ->
    value_type v ->
    |- v <$ t.
Proof.
  apply match_valty__sub_r_complete.
Qed.

(* ================================================================= *)
(** *** Correctness with respect to Declarative Subtyping *)
(* ================================================================= *)

(* ----------------------------------------------------------------- *)
(** **** Soundness *)
(* ----------------------------------------------------------------- *)

(** Reductive subtyping implies declarative. *)
(* DEP: mk_nf__sub_d2 *)
Theorem sub_r__sound : forall (t1 t2 : ty),
    |- t1 << t2 ->
    (|- t1 << t2)%btj.
Proof.
  intros t1 t2 Hsub; induction Hsub;
    try solve [
          constructor
        | apply SD_Trans with treal; constructor ].
  - (* Pair *)
    constructor; assumption.
  - (* UnionL *)
    constructor; assumption.
  - (* UnionR1 *)
    apply union_right_1; assumption.
  - (* UnionR2 *)
    apply union_right_2; assumption.
  - (* NF *)
    apply SD_Trans with (MkNF(t)).
    apply mk_nf__sub_d2.
    assumption.
Qed.

(* ----------------------------------------------------------------- *)
(** **** Completeness *)
(* ----------------------------------------------------------------- *)

(** Declarative subtyping implies reductive. *)
(* DEP: sub_r__reflexive, sub_r__transitive *)
Theorem sub_r__complete : forall (t1 t2 : ty),
    (|- t1 << t2)%btj ->
    |- t1 << t2.
Proof.
  intros t1 t2 Hsub; induction Hsub;
    try solve [constructor].
  - (* Refl *)
    apply sub_r__reflexive.
  - (* Trans *)
    apply sub_r__transitive with t2; assumption.
  - (* RealUnion *)
    apply SR_NormalForm; simpl; constructor;
      [apply SR_UnionR1 | apply SR_UnionR2]; constructor.
  - (* NumUnion *)
    apply SR_NormalForm; simpl; constructor;
      [apply SR_UnionR1 | apply SR_UnionR2]; do 2 constructor.
  - (* Pair *)
    constructor; assumption.
  - (* UnionL *)
    constructor; assumption.
  - (* UnionR1 *)
    apply SR_UnionR1; apply sub_r__reflexive.
  - (* UnionR2 *)
    apply SR_UnionR2; apply sub_r__reflexive.
  - (* Distr1 *)
    apply mk_nf_sub_r__sub_r. apply mk_nf__distr11.
  - (* Distr2 *)
    apply mk_nf_sub_r__sub_r. apply mk_nf__distr21.
Qed.

(* ================================================================= *)
(** *** Decidability *)
(* ================================================================= *)

(** [t1 << t2] is decidable. *)
(* DEP: mk_nf__in_nf, nf_sub_r__decidable *)
Theorem sub_r__decidable : forall (t1 t2 : ty),
    Decidable.decidable (|- t1 << t2).
Proof.
  intros t1 t2.
  assert (Hnf: InNF(MkNF(t1))) by (apply mk_nf__in_nf).
  pose proof (nf_sub_r__decidable _ t2 Hnf) as Hdec.
  destruct Hdec as [Hdec | Hdec].
  - left; apply SR_NormalForm; assumption.
  - right; intros Hcontra.
    apply sub_r__mk_nf_sub_r1 in Hcontra.
    contradiction.
Qed.
