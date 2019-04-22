(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(*    MiniJl:
        Decidable, Tag-Based Semantic Subtyping 
        for Nominal Types, Pairs, and Unions.  *)

(** * MiniJl: Propositions about Reductive Subtyping *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

Add LoadPath "../..". (* root directory of the repo *)

Require Import Mechanization.Aux.Identifier.

Require Import Mechanization.MiniJl.BaseDefs.
Require Import Mechanization.MiniJl.BaseProps.
Require Import Mechanization.MiniJl.MatchProps.

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.

Close Scope btj_scope.
Open  Scope btjm_scope.
Open  Scope btjnf_scope.
Open  Scope btjr_scope.


(* ################################################################# *)
(** ** Auxiliary Statements *)
(* ################################################################# *)

(* ================================================================= *)
(** *** Union of Normal Form *)
(* ================================================================= *)

(* DEP: mk_nf_nf__equal *)
Lemma union_nf_sub_r__components_sub_r : forall (t1 t2 t' : ty),
    |- TUnion t1 t2 << t' ->
    InNF(t1) -> InNF(t2) ->
    |- t1 << t' /\ |- t2 << t'.
Proof.
  intros t1 t2 t' H. remember (TUnion t1 t2) as t eqn:Heq.
  induction H; intros Hnf1 Hnf2; try solve [inversion Heq].
  - (* UnionL *)
    inversion Heq; subst. split; assumption.
  - (* UnionR1 *)
    inversion Heq; subst. specialize (IHsub_r H0).
    split; (apply SR_UnionR1 || apply SR_UnionR2); tauto. 
  - (* UnionR2 *)
    inversion Heq; subst. specialize (IHsub_r H0).
    split; (apply SR_UnionR2 || apply SR_UnionR2); tauto.
  - (* NF *)
    subst. simpl in *. apply IHsub_r; try assumption.
    rewrite (mk_nf_nf__equal _ Hnf1).
    rewrite (mk_nf_nf__equal _ Hnf2).
    reflexivity.
Qed.

(* ================================================================= *)
(** *** About [unite_pairs] *)
(* ================================================================= *)

(* DEP: sub_r__rflxv, unite_pairs_t_union, unite_pairs_union_t,
        union_in_nf__components_in_nf, 
        mk_nf_nf__equal, mk_nf__in_nf *)
Lemma unite_pairs_of_nf__preserves_sub_r : forall (t1 t2 t1' t2' : ty),
    |- t1 << t1' -> 
    |- t2 << t2' -> 
    InNF(t1) -> InNF(t1') ->
    InNF(t2) -> InNF(t2') ->
    |- unite_pairs t1 t2 << unite_pairs t1' t2'.
Proof.
  intros ta tb ta' tb' Hsub1.
  generalize dependent tb'. generalize dependent tb.
  induction Hsub1; intros tb tb' Hsub2;
    try solve [
          induction Hsub2; intros Hnfa Hnfa' Hnfb Hnfb';
          try solve [
                simpl; constructor; constructor; assumption
              (* UnionL *)
              | rewrite unite_pairs_t_union; try resolve_not_union;
                destruct (union_in_nf__components_in_nf _ _ Hnfb) as [Hnfb1 Hnfb2];
                constructor; [apply IHHsub2_1 | apply IHHsub2_2];
                assumption || constructor
              (* UnionR1 *)
              | rewrite unite_pairs_t_union; try resolve_not_union;
                destruct (union_in_nf__components_in_nf _ _ Hnfb') as [Hnfb1 Hnfb2];
                apply SR_UnionR1; apply IHHsub2; assumption || constructor
              (* UnionR2 *)
              | rewrite unite_pairs_t_union; try resolve_not_union;
                destruct (union_in_nf__components_in_nf _ _ Hnfb') as [Hnfb1 Hnfb2];
                apply SR_UnionR2; apply IHHsub2; assumption || constructor
              (* NF *)
              | rewrite <- (mk_nf_nf__equal _ Hnfb);
                apply IHHsub2; try assumption; apply mk_nf__in_nf ]
        ].
  - (* UnionL, tb *)
    intros Hnfa Hnfa' Hnfb Hnfb'. rewrite unite_pairs_union_t.
    destruct (union_in_nf__components_in_nf _ _ Hnfa) as [Hnfa1 Hnfa2].
    constructor; [apply IHHsub1_1 | apply IHHsub1_2]; assumption.
  - (* UnionR1, tb *)
    intros Hnfa Hnfa' Hnfb Hnfb'. rewrite unite_pairs_union_t.
    destruct (union_in_nf__components_in_nf _ _ Hnfa') as [Hnfa1 Hnfa2].
    apply SR_UnionR1; apply IHHsub1; assumption.
  - (* UnionR2, tb *)
    intros Hnfa Hnfa' Hnfb Hnfb'. rewrite unite_pairs_union_t.
    destruct (union_in_nf__components_in_nf _ _ Hnfa') as [Hnfa1 Hnfa2].
    apply SR_UnionR2; apply IHHsub1; assumption.
  - (* NF, tb *)
    intros Hnfa Hnfa' Hnfb Hnfb'.
    rewrite <- (mk_nf_nf__equal _ Hnfa).
    apply IHHsub1; try assumption. apply mk_nf__in_nf.
Qed.

(* DEP: unite_pairs_t_union, unite_pairs_union_t,
        union_in_nf__components_in_nf, union_nf_sub_r__components_sub_r *)
Lemma unite_pairs_of_nf__preserves_sub_r1 : forall (t1 t2 t1' t2' : ty),
    InNF(t1) -> |- t1 << t1' ->
    InNF(t2) -> |- t2 << t2' ->
    |- unite_pairs t1 t2 << TPair t1' t2'.
Proof.
  intros ta; induction ta;
    intros tb; induction tb;
      intros ta' tb' Hnf1 Hsub1 Hnf2 Hsub2;
      try solve [
            simpl; constructor; assumption
          | match goal with
            | [Hnf1: InNF(?t), Hnf2: InNF(TUnion ?t1 ?t2),
               Hsub: |- TUnion ?t1 ?t2 << _
               |- |- unite_pairs ?t (TUnion ?t1 ?t2) << TPair _ _] =>
              rewrite unite_pairs_t_union; try resolve_not_union;
              destruct (union_in_nf__components_in_nf _ _ Hnf2) as [Hnfb1 Hnfb2];
              destruct (union_nf_sub_r__components_sub_r _ _ _ Hsub Hnfb1 Hnfb2) as [Hsubb1 Hsubb2];
              constructor; [apply IHtb1 | apply IHtb2]; assumption
            | [Hnf1: InNF(?t), Hnf2: InNF(TUnion ?t1 ?t2),
               Hsub: |- TUnion ?t1 ?t2 << _
               |- |- unite_pairs (TUnion ?t1 ?t2) ?t << TPair _ _] =>
              rewrite unite_pairs_union_t;
              destruct (union_in_nf__components_in_nf _ _ Hnf2) as [Hnfb1 Hnfb2];
              destruct (union_nf_sub_r__components_sub_r _ _ _ Hsub Hnfb1 Hnfb2) as [Hsubb1 Hsubb2];
              constructor; [apply IHta1 | apply IHta2]; assumption
            end
          ].
Qed.

(* ================================================================= *)
(** *** About [MkNF] *)
(* ================================================================= *)

(* DEP: unite_pairs_of_nf__preserves_sub_r1 *)
Lemma sub_r__mk_nf_sub_r1 : forall (t t' : ty),
    |- t << t' ->
    |- MkNF(t) << t'.
Proof.
  intros t t' Hsub; induction Hsub;
    try solve [simpl; constructor; constructor].
  - (* Pair *)
    simpl.
    apply unite_pairs_of_nf__preserves_sub_r1;
      assumption || apply mk_nf__in_nf.
  - (* Union *)
    simpl. constructor; assumption.
  - (* UnionR1 *)
    apply SR_UnionR1; assumption.
  - (* UnionR2 *)
    apply SR_UnionR2; assumption.
  - (* NF *)
    assumption.
Qed.

(* DEP: unite_pairs_of_nf__preserves_sub_r1, mk_nf__in_nf *)
Lemma mk_nf__sub_r1 : forall (t : ty),
    |- MkNF(t) << t.
Proof.
  intros t.
  apply sub_r__mk_nf_sub_r1.
  apply sub_r__rflxv.
Qed.

Lemma mk_nf__sub_r2 : forall (t : ty),
    |- t << MkNF(t).
Proof.
  intros t.
  apply SR_NormalForm.
  apply sub_r__rflxv.
Qed.

(* ================================================================= *)
(** *** Related to Transitivity *)
(* ================================================================= *)

(* DEP: sub_r__mk_nf_sub_r1, union_nf_sub_r__components_sub_r *)
Lemma union_sub_r__components_sub_r : forall (t1 t2 t' : ty),
    |- TUnion t1 t2 << t' ->
    |- t1 << t' /\ |- t2 << t'.
Proof.
  intros t1 t2 t' Hsub.
  pose proof (sub_r__mk_nf_sub_r1 _ _ Hsub).
  simpl in H.
  assert (Hsubnf: |- MkNF(t1) << t' /\ |- MkNF(t2) << t').
  { apply union_nf_sub_r__components_sub_r;
      assumption || apply mk_nf__in_nf. }
  split; apply SR_NormalForm; tauto.
Qed.

(* DEP: sub_r_value_types__equal, union_in_nf__components_in_nf, 
        mk_nf_nf__equal *)
Lemma sub_r_nf__transitive : forall (t1 t2 t3 : ty),
    |- t1 << t2 ->
    InNF(t1) -> InNF(t2) ->
    |- t2 << t3 ->
    |- t1 << t3.
Proof.
  intros t1 t2 t3 Hsub1. generalize dependent t3.
  induction Hsub1; intros t3 Hnf1 Hnf2 Hsub2;
    try solve [
          assumption
        | inversion Hnf2; subst;
          match goal with [H: value_type _ |- _] => inversion H end
        ].
  - (* Pair *)
    inversion Hnf1; subst. inversion Hnf2; subst.
    inversion H; inversion H0; subst.
    pose proof (sub_r_value_types__equal _ _ Hsub1_1 H3 H7).
    pose proof (sub_r_value_types__equal _ _ Hsub1_2 H4 H8).
    subst. assumption.
  - (* UnionL *)
    destruct (union_in_nf__components_in_nf _ _ Hnf1) as [Hnfa1 Hnfa2].
    constructor; [apply IHHsub1_1 | apply IHHsub1_2]; assumption.
  - (* UnionR1 *)
    destruct (union_in_nf__components_in_nf _ _ Hnf2) as [Hnfa1 Hnfa2].
    apply IHHsub1; try assumption.
    pose proof (union_nf_sub_r__components_sub_r _ _ _ Hsub2 Hnfa1 Hnfa2); tauto.
  - (* UnionR2 *)
    destruct (union_in_nf__components_in_nf _ _ Hnf2) as [Hnfa1 Hnfa2].
    apply IHHsub1; try assumption.
    pose proof (union_nf_sub_r__components_sub_r _ _ _ Hsub2 Hnfa1 Hnfa2); tauto.
  - (* NF *)
    rewrite mk_nf_nf__equal in IHHsub1; try assumption.
    apply IHHsub1; assumption.
Qed.


(* ################################################################# *)
(** ** Properties related to matching *)
(* ################################################################# *)

(* ================================================================= *)
(** *** Correctness of Subtyping with respect to Matching *)
(* ================================================================= *)

Theorem match_ty__sub_r_sound : forall (v t : ty),
    |- v <$ t ->
    |- v << t.
Proof.
  intros v t H; induction H; try solve [constructor].
  (* Pair *)   constructor; assumption.
  (* Union1 *) apply SR_UnionR1; assumption.
  (* Union2 *) apply SR_UnionR2; assumption.
Qed.

(* ================================================================= *)
(** ** Matching value Type is Complete for Subtyping *)
(* ================================================================= *)

(* DEP: match_valty__rflxv, mk_nf_valty__equal *)
Theorem match_valty__sub_r_complete : forall (v t : ty),
    |- v << t ->
    value_type v ->
    |- v <$ t.
Proof.
  intros v t H; induction H; subst; intros Hval;
    try solve [constructor | inversion Hval].
  - (* Pair *)
    inversion Hval; subst.
    constructor; tauto.
  - (* UnionR1 *)
    apply MT_Union1; tauto.
  - (* UnionR2 *)
    apply MT_Union2; tauto.
  - (* NF *)
    rewrite (mk_nf_valty__equal _ Hval) in *.
    tauto.
Qed.


(* ################################################################# *)
(** ** Properties related to Normal Form *)
(* ################################################################# *)

(** If types are subtypes, their normal forms are also subtypes. *)
(* DEP: unite_pairs_of_nf__preserves_sub_r, 
        mk_nf__in_nf, mk_nf__idempotent *)
Lemma sub_r__mk_nf_sub_r : forall (t t' : ty),
    |- t << t' ->
    |- MkNF(t) << MkNF(t').
Proof.
  intros t t' Hsub; induction Hsub;
    try solve [simpl; do 4 constructor].
  - (* Pair *)
    simpl.
    apply unite_pairs_of_nf__preserves_sub_r;
      assumption || apply mk_nf__in_nf.
  - (* Union *)
    simpl. constructor; assumption.
  - (* UnionR1 *)
    apply SR_UnionR1; assumption.
  - (* UnionR2 *)
    apply SR_UnionR2; assumption.
  - (* NF *)
    rewrite <- mk_nf__idempotent. assumption.
Qed.

(* DEP: mk_nf__in_nf *)
Lemma mk_nf_sub_r__sub_r : forall (t t' : ty),
    |- MkNF(t) << MkNF(t') ->
    |- t << t'.
Proof.
  intros t t' Hsub.
  apply SR_NormalForm.
  apply sub_r_nf__transitive with (MkNF(t')); try (apply mk_nf__in_nf).
  assumption. apply  mk_nf__sub_r1.
Qed.

(* DEP: match_ty__sub_r_sound, match_valty__rflxv *)
Theorem nf_sem_sub__sub_r : forall (t : ty),
    InNF(t) ->
    forall (t' : ty),
      ||- [t] <= [t'] ->
      |- t << t'.
Proof.
  intros t Hnf; induction Hnf; intros t' Hval;
    unfold sem_sub.
  - (* Value *)
    apply match_ty__sub_r_sound. apply Hval.
    assumption. apply match_valty__rflxv. assumption.
  - (* Union *)
    constructor; [apply IHHnf1 | apply IHHnf2]; intros v Hv Hsub;
      try assumption; apply Hval; try assumption.
    apply MT_Union1; assumption.
    apply MT_Union2; assumption.
Qed.


(* ################################################################# *)
(** ** Properties related to Declarative Subtyping *)
(* ################################################################# *)

(* ================================================================= *)
(** *** Reflexivity *)
(* ================================================================= *)

(* DEP: sub_r__rflxv *)
Lemma sub_r__reflexive : forall (t : ty),
    |- t << t.
Proof.
  apply sub_r__rflxv.
Qed.

(* ================================================================= *)
(** *** Transitivity *)
(* ================================================================= *)

(* DEP: sub_r__mk_nf_sub_r, sub_r_nf__transitive,
        mk_nf__in_nf, union_sub_r__components_sub_r *)
Lemma sub_r__transitive : forall (t1 t2 t3 : ty),
    |- t1 << t2 ->
    |- t2 << t3 ->
    |- t1 << t3.
Proof.
  intros t1 t2 t3 Hsub1. generalize dependent t3.
  induction Hsub1; intros t3 Hsub2;
    try (apply sub_r__mk_nf_sub_r1 in Hsub2; simpl in Hsub2;
         destruct (union_sub_r__components_sub_r _ _ _ Hsub2) as [Hsub21 Hsub22]);
    try (destruct (union_sub_r__components_sub_r _ _ _ Hsub21));
    try auto.
  (* Pair *)
  remember (TPair t1' t2') as tm eqn:Heq.
  induction Hsub2; try solve [inversion Heq].
  - (* Pair *)
    inversion Heq; subst.
    constructor; auto.
  - (* UnionR1 *)
    apply SR_UnionR1; tauto.
  - (* UnionR2 *)
    apply SR_UnionR2; tauto.
  - (* NF *)
    inversion Heq; subst. clear H.
    assert (Hsub1: |- TPair t1 t2 << TPair t1' t2') by (constructor; assumption).
    pose proof (sub_r__mk_nf_sub_r _ _ Hsub1) as Hsub1nf.
    apply SR_NormalForm.
    apply sub_r_nf__transitive with (MkNF( TPair t1' t2'));
      assumption || apply mk_nf__in_nf.
Qed.

(* ================================================================= *)
(** *** Distributivity *)
(* ================================================================= *)

(* ----------------------------------------------------------------- *)
(** **** Aux *)
(* ----------------------------------------------------------------- *)

(* DEP: unite_pairs_t_union, unite_pairs_union_t,
        sub_r__reflexive, sub_r__transitive *)
Lemma unite_pairs__distr21 : forall (t1 t21 t22 : ty),
    InNF(t1) ->
    |- unite_pairs t1 (TUnion t21 t22) <<
       TUnion (unite_pairs t1 t21) (unite_pairs t1 t22).
Proof.
  intros t1 t21 t22 Hnf1.
  generalize dependent t22. generalize dependent t21.
  induction Hnf1; intros t21 t22.
  - (* Value *)
    rewrite unite_pairs_t_union; try resolve_not_union.
    apply sub_r__reflexive. subst; inversion H.
  - (* Union *)
    repeat rewrite unite_pairs_union_t.
    constructor.
    + apply sub_r__transitive with (TUnion (unite_pairs t1 t21) (unite_pairs t1 t22)).
      apply IHHnf1_1. constructor.
      apply SR_UnionR1; apply SR_UnionR1; apply sub_r__reflexive.
      apply SR_UnionR2; apply SR_UnionR1; apply sub_r__reflexive.
    + apply sub_r__transitive with (TUnion (unite_pairs t2 t21) (unite_pairs t2 t22)).
      apply IHHnf1_2. constructor.
      apply SR_UnionR1; apply SR_UnionR2; apply sub_r__reflexive.
      apply SR_UnionR2; apply SR_UnionR2; apply sub_r__reflexive.
Qed.

(* ----------------------------------------------------------------- *)
(** **** Main Properties *)
(* ----------------------------------------------------------------- *)

(* DEP: unite_pairs_union_t, sub_r__reflexive *)
Lemma mk_nf__distr11 : forall (t11 t12 t2 : ty),
    |- MkNF(TPair (TUnion t11 t12) t2) << MkNF(TUnion (TPair t11 t2) (TPair t12 t2)).
Proof.
  intros t11 t12 t2.
  change (|- MkNF( TPair (TUnion t11 t12) t2) << TUnion (MkNF(TPair t11 t2)) (MkNF(TPair t12 t2))).
  change (|- unite_pairs (MkNF(TUnion t11 t12)) (MkNF(t2)) <<
             TUnion (MkNF(TPair t11 t2)) (MkNF(TPair t12 t2))).
  change (|- unite_pairs (TUnion (MkNF(t11)) (MkNF(t12))) (MkNF(t2)) <<
             TUnion (MkNF(TPair t11 t2)) (MkNF(TPair t12 t2))).
  rewrite unite_pairs_union_t.
  apply sub_r__reflexive.
Qed.

(* DEP: unite_pairs__distr21, mk_nf__in_nf *)
Lemma mk_nf__distr21 : forall (t1 t21 t22 : ty),
    |- MkNF(TPair t1 (TUnion t21 t22)) << MkNF(TUnion (TPair t1 t21) (TPair t1 t22)).
Proof.
  intros t1 t21 t22.
  change (|- MkNF(TPair t1 (TUnion t21 t22)) << TUnion (MkNF(TPair t1 t21)) (MkNF(TPair t1 t22))).
  change (|- unite_pairs (MkNF(t1)) (TUnion (MkNF(t21)) (MkNF(t22))) <<
             TUnion (MkNF(TPair t1 t21)) (MkNF(TPair t1 t22))).
  change (|- unite_pairs (MkNF(t1)) (TUnion (MkNF(t21)) (MkNF(t22))) <<
                               TUnion (unite_pairs (MkNF(t1)) (MkNF(t21))) (unite_pairs (MkNF(t1)) (MkNF(t22)))).
  apply unite_pairs__distr21.
  apply mk_nf__in_nf.
Qed.


(* ################################################################# *)
(** ** Decidability *)
(* ################################################################# *)

(** Reductive subtyping of a normalized term on the left 
    is decidable. *)
(* DEP: match_ty__dcdbl, match_ty__sub_r_sound *)
Lemma nf_sub_r__decidable : forall (t1 t2 : ty),
    InNF(t1) ->
    Decidable.decidable (|- t1 << t2).
Proof.
  intros t1 t2 Hnf1. generalize dependent t2.
  induction Hnf1.
  - (* Value *)
    intros t2. destruct (match_ty__dcdbl v t2) as [Hm | Hm].
    + left. apply match_ty__sub_r_sound. assumption.
    + right; intros Hcontra.
      assert (Hcontra': |- v <$ t2)
        by (apply match_valty__sub_r_complete; assumption).
      contradiction.
  - (* Union *)
    intros t'.
    destruct (IHHnf1_1 t') as [IH1 | IH1];
      destruct (IHHnf1_2 t') as [IH2 | IH2];
      try solve [
            right; intros Hcontra;
            destruct (union_sub_r__components_sub_r _ _ _ Hcontra) as [Hsub1 Hsub2];
            contradiction ].
    left; constructor; assumption.
Qed.
