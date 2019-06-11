(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(*    FullAtomicJl:
        Decidable, Tag-Based (Atomically) Semantic Subtyping 
        for Nominal Types, Pairs, and Unions.  *)

(** * FullAtomicJl: Main Propositions *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

Add LoadPath "../..". (* root directory of the repo *)

Require Import Mechanization.Aux.Identifier.

Require Import Mechanization.FullAtomicJl.BaseDefs.
Require Import Mechanization.FullAtomicJl.BaseProps.
Require Import Mechanization.FullAtomicJl.MatchProps.
Require Import Mechanization.FullAtomicJl.SemSubProps.
Require Import Mechanization.FullAtomicJl.DeclSubProps.
Require Import Mechanization.FullAtomicJl.RedSubProps.

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
(** ** On Reductive Subtyping *)
(* ################################################################# *)

Close Scope btj_scope.
Open  Scope btjr_scope.

(* ================================================================= *)
(** *** Relation to Matching *)
(* ================================================================= *)

Theorem match_ty__sub_r_sound' : forall (v t : ty),
    valid v ->
    |- v <$ t ->
    |- v << t.
Proof.
  apply match_ty__sub_r_sound.
Qed.

Theorem match_valty__sub_r_complete' : forall (v t : ty),
    valid v -> valid t ->
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
    valid t1 ->
    |- t1 << t2 ->
    (|- t1 << t2)%btj.
Proof.
  intros t1 t2 HTY1 Hsub; induction Hsub;
    try solve [
          constructor
        | apply SD_Trans with treal; constructor ].
  - (* Pair *)
    inversion HTY1; subst.
    constructor; tauto.
  - (* UnionL *)
    inversion HTY1; subst.
    constructor; tauto.
  - (* UnionR1 *)
    apply union_right_1; tauto.
  - (* UnionR2 *)
    apply union_right_2; tauto.
  - (* NF *)
    apply SD_Trans with (MkNF(t)).
    apply mk_nf__sub_d2.
    assumption. apply IHHsub.
    apply mk_nf__preserves_valid; assumption.
Qed.

(* ----------------------------------------------------------------- *)
(** **** Completeness *)
(* ----------------------------------------------------------------- *)

(** Declarative subtyping implies reductive. *)
(* DEP: sub_r__reflexive, sub_r__transitive *)
Theorem sub_r__complete : forall (t1 t2 : ty),
    valid t1 -> valid t2 ->
    (|- t1 << t2)%btj ->
    |- t1 << t2.
Proof.
  intros t1 t2 HTY1 HTY2 Hsub; induction Hsub;
    try solve [constructor].
  - (* Refl *)
    apply sub_r__reflexive; assumption.
  - (* Trans *)
    pose proof (sub_d__valid1 _ _ Hsub2) as HTY3.
    apply sub_r__transitive with t2; tauto.
  - (* Pair *)
    inversion HTY1; inversion HTY2; subst.
    constructor; tauto.
  - (* UnionL *)
    inversion HTY1; subst.
    constructor; tauto.
  - (* UnionR1 *)
    inversion HTY2; subst.
    apply SR_UnionR1; apply sub_r__reflexive; tauto.
  - (* UnionR2 *)
    inversion HTY2; subst.
    apply SR_UnionR2; apply sub_r__reflexive; tauto.
  - (* Distr1 *)
    inversion HTY1; inversion HTY2; subst.
    inversion H1; inversion H5; inversion H6; subst.
    apply mk_nf_sub_r__sub_r; try solve [constructor; assumption].
    apply mk_nf__distr11; assumption.
  - (* Distr2 *)
    inversion HTY1; inversion HTY2; subst.
    inversion H2; inversion H5; inversion H6; subst.
    apply mk_nf_sub_r__sub_r; try solve [constructor; assumption].
    apply mk_nf__distr21; tauto.
Qed.

(* ================================================================= *)
(** *** Decidability *)
(* ================================================================= *)

(** [t1 << t2] is decidable. *)
(* DEP: mk_nf__in_nf, nf_sub_r__decidable *)
Theorem sub_r__decidable : forall (t1 t2 : ty),
    valid t1 -> valid t2 ->
    Decidable.decidable (|- t1 << t2).
Proof.
  intros t1 t2 HTY1 HTY2.
  assert (Hnf: InNF(MkNF(t1))) by (apply mk_nf__in_nf; assumption).
  pose proof (nf_sub_r__decidable _ t2 Hnf) as Hdec.
  destruct Hdec as [Hdec | Hdec]; try assumption.
  - left; apply SR_NormalForm; assumption.
  - right; intros Hcontra.
    apply sub_r__mk_nf_sub_r1 in Hcontra.
    contradiction. assumption.
Qed.

(*
Eval compute in sub_r__decidable tint (TUnion tint tflt).
*) 

(* ################################################################# *)
(** ** On Declarative Subtyping *)
(* ################################################################# *)

Close Scope btjr_scope.
Open  Scope btj_scope.

(* ================================================================= *)
(** *** Relation to Matching *)
(* ================================================================= *)

Theorem match_ty__sub_d_sound' : forall (v t : ty),
    valid v ->
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
(** *** Semantic Soundness and Completeness *)
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
    valid t1 -> valid t2 ->
    ||- [t1] <= [t2] ->
    |- t1 << t2.
Proof.
  intros t1 t2 HTY1 HTY2 Hsem.
  (* exists nt1 = NF(t1) *)
  pose proof (nf_exists t1 HTY1) as [tn1 [Hnf1 [Hsub1 Hsub2]]].
  (* t1 << tn1 << t2 *)
  apply SD_Trans with tn1; try assumption.
  apply nf_sem_sub__sub_d; try assumption.
  (* [tn1] <= [t2] *)
  unfold sem_sub in *. intros v Hv Hm1.
  apply Hsem. assumption.
  apply match_valty__transitive_on_sub_d with tn1; assumption.
Qed. 
      

