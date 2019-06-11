(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(*    FullAtomicJl:
        Decidable, Tag-Based Semantic Subtyping 
        for Nominal Types, Pairs, and Unions.  *)

(** * FullAtomicJl: Propositions about Reductive Subtyping *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

Add LoadPath "../..". (* root directory of the repo *)

Require Import Mechanization.Aux.Identifier.

Require Import Mechanization.FullAtomicJl.BaseDefs.
Require Import Mechanization.FullAtomicJl.BaseProps.
Require Import Mechanization.FullAtomicJl.MatchProps.

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
        mk_nf_nf__equal, mk_nf__in_nf, mk_nf__preserves_valid *)
Lemma unite_pairs_of_nf__preserves_sub_r : forall (t1 t2 t1' t2' : ty),
    valid t1 ->
    valid t2 ->
    |- t1 << t1' -> 
    |- t2 << t2' -> 
    InNF(t1) -> InNF(t1') ->
    InNF(t2) -> InNF(t2') ->
    |- unite_pairs t1 t2 << unite_pairs t1' t2'.
Proof.
  intros ta tb ta' tb' HTY1 HTY2 Hsub1.
  generalize dependent tb'; generalize dependent tb;
    induction Hsub1; intros tb HTY2 tb' Hsub2;
    try solve [ 
          induction Hsub2; intros Hnfa Hnfa' Hnfb Hnfb';
          try solve [
                simpl; constructor; constructor; assumption
              (* UnionL *)
              | inversion HTY2; subst;
                rewrite unite_pairs_t_union; try resolve_not_union;
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
                pose proof (mk_nf__preserves_valid _ HTY2) as HTYnf;
                apply IHHsub2; try assumption; apply mk_nf__in_nf; assumption ]
        ].
  - (* UnionL, tb *)
    intros Hnfa Hnfa' Hnfb Hnfb'. rewrite unite_pairs_union_t.
    destruct (union_in_nf__components_in_nf _ _ Hnfa) as [Hnfa1 Hnfa2].
    inversion HTY1; subst.
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
    apply IHHsub1; try assumption.
    apply mk_nf__preserves_valid; assumption.
    apply mk_nf__in_nf; assumption.
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
    valid t ->
    |- t << t' ->
    |- MkNF(t) << t'.
Proof.
  intros t t' HTYt Hsub; induction Hsub;
    try solve [simpl; constructor; constructor].
  - (* Pair *)
    simpl. inversion HTYt; subst.
    apply unite_pairs_of_nf__preserves_sub_r1; 
      tauto || apply mk_nf__in_nf; assumption.
  - (* Union *)
    simpl. inversion HTYt; subst.
    constructor; tauto.
  - (* UnionR1 *)
    apply SR_UnionR1; tauto.
  - (* UnionR2 *)
    apply SR_UnionR2; tauto.
  - (* NF *)
    assumption.
Qed.

(* DEP: unite_pairs_of_nf__preserves_sub_r1, mk_nf__in_nf *)
Lemma mk_nf__sub_r1 : forall (t : ty),
    valid t ->
    |- MkNF(t) << t.
Proof.
  intros t HTY.
  apply sub_r__mk_nf_sub_r1. assumption.
  apply sub_r__rflxv; assumption.
Qed.

(* DEP: mk_nf__preserves_valid, sub_r__rflxv *)
Lemma mk_nf__sub_r2 : forall (t : ty),
    valid t ->
    |- t << MkNF(t).
Proof.
  intros t HTY.
  apply SR_NormalForm. apply sub_r__rflxv.
  apply mk_nf__preserves_valid; assumption.
Qed.

(* ================================================================= *)
(** *** Related to Transitivity *)
(* ================================================================= *)

(* DEP: sub_r__mk_nf_sub_r1, union_nf_sub_r__components_sub_r *)
Lemma union_sub_r__components_sub_r : forall (t1 t2 t' : ty),
    valid t1 -> valid t2 ->
    |- TUnion t1 t2 << t' ->
    |- t1 << t' /\ |- t2 << t'.
Proof.
  intros t1 t2 t' HTY1 HTY2 Hsub.
  assert (HTY: valid (TUnion t1 t2)) by (constructor; assumption).
  pose proof (sub_r__mk_nf_sub_r1 _ _ HTY Hsub).
  simpl in H.
  assert (Hsubnf: |- MkNF(t1) << t' /\ |- MkNF(t2) << t').
  { apply union_nf_sub_r__components_sub_r;
      assumption || apply mk_nf__in_nf; assumption. }
  split; apply SR_NormalForm; tauto.
Qed.

(* DEP: sub_r_value_types__equal, union_in_nf__components_in_nf, 
        mk_nf_nf__equal, mk_nf__in_nf, mk_nf__preserves_valid *)
Lemma sub_r_nf__transitive : forall (t1 t2 t3 : ty),
    valid t2 ->
    |- t1 << t2 ->
    InNF(t1) -> InNF(t2) ->
    |- t2 << t3 ->
    |- t1 << t3.
Proof.
  intros t1 t2 t3 HTY2 Hsub1. generalize dependent t3.
  induction Hsub1; intros t3 Hnf1 Hnf2 Hsub2;
    try solve [
          assumption
        | inversion Hnf2; subst;
          match goal with [H: value_type _ |- _] => inversion H end
        | remember treal as t2 eqn:Heq2; induction Hsub2;
          inversion Heq2; subst; try solve [constructor | auto]
        | remember tnum as t2 eqn:Heq2; induction Hsub2;
          inversion Heq2; subst; try solve [constructor | auto]
        ].  
  - (* Pair *)
    inversion Hnf1; subst. inversion Hnf2; subst.
    inversion HTY2; subst.
    inversion H; inversion H0; subst.
    remember (TPair t1' t2') as tx eqn:Heqx; induction Hsub2;
      inversion Heqx; subst.
    + (* Pair *)
      constructor; [apply IHHsub1_1 | apply IHHsub1_2];
        try assumption || constructor; assumption.
    + (* UnionR1 *)
      apply SR_UnionR1; auto.
    + (* UnionR2 *)
      apply SR_UnionR2; auto.
    + (* NF *)
      apply IHHsub2.
      apply mk_nf_nf__equal; assumption.
      apply mk_nf__preserves_valid; assumption.
      apply mk_nf__in_nf; assumption.
      rewrite mk_nf_nf__equal; assumption.
  - (* UnionL *)
    destruct (union_in_nf__components_in_nf _ _ Hnf1) as [Hnfa1 Hnfa2].
    constructor; [apply IHHsub1_1 | apply IHHsub1_2]; assumption.
  - (* UnionR1 *)
    inversion HTY2; subst.
    destruct (union_in_nf__components_in_nf _ _ Hnf2) as [Hnfa1 Hnfa2].
    apply IHHsub1; try assumption.
    pose proof (union_nf_sub_r__components_sub_r _ _ _ Hsub2 Hnfa1 Hnfa2); tauto.
  - (* UnionR2 *)
    inversion HTY2; subst.
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
    valid v ->
    |- v <$ t ->
    |- v << t.
Proof.
  intros v t HTYv H; induction H;
    try solve [constructor | inversion HTYv].
  - (* Pair *)
    inversion HTYv; subst.
    constructor; tauto.
  - (* Union1 *)
    apply SR_UnionR1; tauto.
  - (* Union2 *)
    apply SR_UnionR2; tauto.
Qed.

(* ================================================================= *)
(** ** Matching value Type is Complete for Subtyping *)
(* ================================================================= *)

(* DEP: value_type_valid__atom, mk_nf_nf__equal,
        mk_nf__preserves_valid, mk_nf__preserves_value_type *)
Theorem match_valty__sub_r_complete : forall (v t : ty),
    valid v -> valid t ->
    |- v << t ->
    value_type v ->
    |- v <$ t.
Proof.
  intros v t HTYv HTYt H; induction H; subst; intros Hval;
    try solve [constructor | inversion Hval].
  - (* Pair *)
    inversion Hval; inversion HTYv; inversion HTYt; subst.
    constructor; tauto.
  - (* UnionR1 *)
    inversion HTYt; subst.
    apply MT_Union1; tauto.
  - (* UnionR2 *)
    inversion HTYt; subst.
    apply MT_Union2; tauto.
  - (* NF *)
    assert (Hnf: InNF(t)) by (constructor; apply value_type_valid__atom; assumption).
    rewrite <- (mk_nf_nf__equal _ Hnf). apply IHsub_r; try assumption.
    apply mk_nf__preserves_valid; assumption.
    apply mk_nf__preserves_value_type; assumption.
Qed.


(* ################################################################# *)
(** ** Properties related to Normal Form *)
(* ################################################################# *)

(** If types are subtypes, their normal forms are also subtypes. *)
(* DEP: unite_pairs_of_nf__preserves_sub_r, 
        mk_nf__in_nf, mk_nf__idempotent,
        mk_nf__preserves_valid *)
Lemma sub_r__mk_nf_sub_r : forall (t t' : ty),
    valid t -> valid t' ->
    |- t << t' ->
    |- MkNF(t) << MkNF(t').
Proof.
  intros t t' HTYt HTYt' Hsub; induction Hsub;
    try solve [simpl; do 4 constructor].
  - (* Pair *)
    simpl. inversion HTYt; inversion HTYt'; subst. 
    apply unite_pairs_of_nf__preserves_sub_r;
      (apply mk_nf__preserves_valid; assumption) || tauto
      ||  apply mk_nf__in_nf; assumption.
  - (* Union *)
    simpl. inversion HTYt; subst.
    constructor; tauto.
  - (* UnionR1 *)
    simpl. inversion HTYt'; subst.
    apply SR_UnionR1; tauto.
  - (* UnionR2 *)
    simpl. inversion HTYt'; subst.
    apply SR_UnionR2; tauto.
  - (* NF *)
    rewrite <- mk_nf__idempotent; try assumption.
    apply IHHsub; try assumption.
    apply mk_nf__preserves_valid; assumption.
Qed.

(* DEP: sub_r_nf__transitive, mk_nf__in_nf,
        mk_nf__preserves_valid, mk_nf__sub_r1 *)
Lemma mk_nf_sub_r__sub_r : forall (t t' : ty),
    valid t -> valid t' ->
    |- MkNF(t) << MkNF(t') ->
    |- t << t'.
Proof.
  intros t t' HTYt HTYt' Hsub.
  apply SR_NormalForm.
  apply sub_r_nf__transitive with (MkNF(t'));
    try (apply mk_nf__in_nf; try assumption) || assumption.
  apply mk_nf__preserves_valid; assumption.
  apply mk_nf__sub_r1; assumption.
Qed.

(*
(* DEP: match_ty__sub_r_sound, match_valty__rflxv *)
Theorem nf_sem_sub__sub_r : forall (t : ty),
    InNF(t) ->
    forall (t' : ty),
      valid t' ->
      ||- [t] <= [t'] ->
      |- t << t'.
Proof.
  intros t Hnf; induction Hnf; intros t' HTYt' Hval;
    unfold sem_sub.
  - (* Value *)
    apply match_ty__sub_r_sound. apply atom__valid; assumption.
    apply Hval. (* assumption. apply match_valty__rflxv. assumption.
  - (* Union *)
    constructor; [apply IHHnf1 | apply IHHnf2]; intros v Hv Hsub;
      try assumption; apply Hval; try assumption.
    apply MT_Union1; assumption.
    apply MT_Union2; assumption.
Qed.
*)
*)

(* ################################################################# *)
(** ** Properties related to Declarative Subtyping *)
(* ################################################################# *)

(* ================================================================= *)
(** *** Reflexivity *)
(* ================================================================= *)

(* DEP: sub_r__rflxv *)
Lemma sub_r__reflexive : forall (t : ty),
    valid t ->
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
    valid t1 -> valid t2 ->
    |- t1 << t2 ->
    |- t2 << t3 ->
    |- t1 << t3.
Proof.
  intros t1 t2 t3 HTY1 HTY2 Hsub1. generalize dependent t3.
  induction Hsub1; intros t3 Hsub2;
    try solve [auto | inversion HTY1; auto];
    try solve [
          remember treal as t2 eqn:Heq2; induction Hsub2;
          inversion Heq2; subst; try solve [constructor | auto]
        | remember tnum as t2 eqn:Heq2; induction Hsub2;
          inversion Heq2; subst; try solve [constructor | auto]
        ].
  - (* Pair *)
    inversion HTY1; inversion HTY2; subst.
    remember (TPair t1' t2') as tm eqn:Heq.
    induction Hsub2; try solve [inversion Heq].
    + (* Pair *)
      inversion Heq; subst.
      constructor; auto.
    + (* UnionR1 *)
      apply SR_UnionR1; tauto.
    + (* UnionR2 *)
      apply SR_UnionR2; tauto.
    + (* NF *)
      inversion Heq; subst. clear H.
      assert (Hsub1: |- TPair t1 t2 << TPair t1' t2') by (constructor; assumption).
      pose proof (sub_r__mk_nf_sub_r _ _ HTY1 HTY2 Hsub1) as Hsub1nf.
      apply SR_NormalForm.
      apply sub_r_nf__transitive with (MkNF( TPair t1' t2'));
        try assumption || apply mk_nf__in_nf; try assumption.
      apply mk_nf__preserves_valid; assumption.
  - (* Union1 *)
    apply (sub_r__mk_nf_sub_r1 _ _ HTY2) in Hsub2; simpl in Hsub2.
    inversion HTY2; subst.
    pose proof (mk_nf__preserves_valid _ H1) as HTYnf1.
    pose proof (mk_nf__preserves_valid _ H2) as HTYnf2.
    destruct (union_sub_r__components_sub_r _ _ _ HTYnf1 HTYnf2 Hsub2) as [Hsub21 Hsub22].
    auto.
  - (* Union2 *)
    apply (sub_r__mk_nf_sub_r1 _ _ HTY2) in Hsub2; simpl in Hsub2.
    inversion HTY2; subst.
    pose proof (mk_nf__preserves_valid _ H1) as HTYnf1.
    pose proof (mk_nf__preserves_valid _ H2) as HTYnf2.
    destruct (union_sub_r__components_sub_r _ _ _ HTYnf1 HTYnf2 Hsub2) as [Hsub21 Hsub22].
    auto.
  - (* NF *)
    apply SR_NormalForm.
    pose proof (mk_nf__preserves_valid _ HTY1) as HTYnf1.
    auto.
Qed.

(* ================================================================= *)
(** *** Distributivity *)
(* ================================================================= *)

(* ----------------------------------------------------------------- *)
(** **** Aux *)
(* ----------------------------------------------------------------- *)

(* DEP: unite_pairs_t_union, unite_pairs_union_t,
        sub_r__reflexive, sub_r__transitive,
        unite_pairs__preserves_nf, nf__valid *)
Lemma unite_pairs__distr21 : forall (t1 t21 t22 : ty),
    InNF(t1) ->
    InNF(t21) -> InNF(t22) ->
    |- unite_pairs t1 (TUnion t21 t22) <<
       TUnion (unite_pairs t1 t21) (unite_pairs t1 t22).
Proof.
  intros t1 t21 t22 Hnf1.
  generalize dependent t22. generalize dependent t21.
  induction Hnf1; intros t21 t22 Hnf21 Hnf22.
  - (* Atom *)
    rewrite unite_pairs_t_union.
    + apply sub_r__reflexive.
      constructor; apply nf__valid; apply unite_pairs__preserves_nf;
        (constructor; assumption) || assumption.
    + intros Hcontra. destruct Hcontra as [tx [ty Heq]].
      induction H; inversion Heq.
  - (* Union *)
    repeat rewrite unite_pairs_union_t.
    constructor.
    + apply sub_r__transitive with (TUnion (unite_pairs t1 t21) (unite_pairs t1 t22)).
      * apply nf__valid.
        apply unite_pairs__preserves_nf; assumption || apply NF_Union; assumption.
      * constructor; apply nf__valid;
        apply unite_pairs__preserves_nf; assumption.
      * apply IHHnf1_1; assumption.
      * constructor; [apply SR_UnionR1 | apply SR_UnionR2];
          apply SR_UnionR1; apply sub_r__reflexive;
          apply nf__valid; apply unite_pairs__preserves_nf; assumption.
    + apply sub_r__transitive with (TUnion (unite_pairs t2 t21) (unite_pairs t2 t22)).
      * apply nf__valid.
        apply unite_pairs__preserves_nf; assumption || apply NF_Union; assumption.
      * constructor; apply nf__valid;
        apply unite_pairs__preserves_nf; assumption.
      * apply IHHnf1_2; assumption.
      * constructor; [apply SR_UnionR1 | apply SR_UnionR2];
          apply SR_UnionR2; apply sub_r__reflexive;
          apply nf__valid; apply unite_pairs__preserves_nf; assumption.
Qed.

(* ----------------------------------------------------------------- *)
(** **** Main Properties *)
(* ----------------------------------------------------------------- *)

(* DEP: unite_pairs_union_t, sub_r__reflexive *)
Lemma mk_nf__distr11 : forall (t11 t12 t2 : ty),
    valid t11 -> valid t12 -> valid t2 ->
    |- MkNF(TPair (TUnion t11 t12) t2) << MkNF(TUnion (TPair t11 t2) (TPair t12 t2)).
Proof.
  intros t11 t12 t2 HTY11 HTY12 HTY2.
  change (|- MkNF( TPair (TUnion t11 t12) t2) << TUnion (MkNF(TPair t11 t2)) (MkNF(TPair t12 t2))).
  change (|- unite_pairs (MkNF(TUnion t11 t12)) (MkNF(t2)) <<
             TUnion (MkNF(TPair t11 t2)) (MkNF(TPair t12 t2))).
  change (|- unite_pairs (TUnion (MkNF(t11)) (MkNF(t12))) (MkNF(t2)) <<
             TUnion (MkNF(TPair t11 t2)) (MkNF(TPair t12 t2))).
  rewrite unite_pairs_union_t.
  apply sub_r__reflexive.
  constructor; apply mk_nf__preserves_valid; constructor; assumption.
Qed.

(* DEP: unite_pairs__distr21, mk_nf__in_nf *)
Lemma mk_nf__distr21 : forall (t1 t21 t22 : ty),
    valid t1 -> valid t21 -> valid t22 ->
    |- MkNF(TPair t1 (TUnion t21 t22)) << MkNF(TUnion (TPair t1 t21) (TPair t1 t22)).
Proof.
  intros t1 t21 t22 HTY1 HTY21 HTY22.
  change (|- MkNF(TPair t1 (TUnion t21 t22)) << TUnion (MkNF(TPair t1 t21)) (MkNF(TPair t1 t22))).
  change (|- unite_pairs (MkNF(t1)) (TUnion (MkNF(t21)) (MkNF(t22))) <<
             TUnion (MkNF(TPair t1 t21)) (MkNF(TPair t1 t22))).
  change (|- unite_pairs (MkNF(t1)) (TUnion (MkNF(t21)) (MkNF(t22))) <<
                               TUnion (unite_pairs (MkNF(t1)) (MkNF(t21))) (unite_pairs (MkNF(t1)) (MkNF(t22)))).
  apply unite_pairs__distr21; apply mk_nf__in_nf; assumption.
Qed.


(* ################################################################# *)
(** ** Examples *)
(* ################################################################# *)

Lemma not__real_sub_r_int :
  ~ (|- treal << tint).
Proof.
  remember treal as t1 eqn:Heq1. remember tint as t2 eqn:Heq2.
  intros Hcontra; induction Hcontra;
    try solve [inversion Heq1 | inversion Heq2].
  subst. tauto.
Qed.

Lemma not__real_sub_r_flt :
  ~ (|- treal << tflt).
Proof.
  remember treal as t1 eqn:Heq1. remember tflt as t2 eqn:Heq2.
  intros Hcontra; induction Hcontra;
    try solve [inversion Heq1 | inversion Heq2].
  subst. tauto.
Qed.

Lemma not__real_sub_r_u_int_flt :
  ~ (|- treal << TUnion tint tflt).
Proof.
  remember treal as t1 eqn:Heq1. remember (TUnion tint tflt) as t2 eqn:Heq2.
  intros Hcontra; induction Hcontra;
    try solve [inversion Heq1 | inversion Heq2].
  - inversion Heq1; inversion Heq2; subst.
    apply not__real_sub_r_int; tauto.
  - inversion Heq1; inversion Heq2; subst.
    apply not__real_sub_r_flt; tauto.
  - subst; tauto.
Qed.


(* ################################################################# *)
(** ** Decidability *)
(* ################################################################# *)

(* ----------------------------------------------------------------- *)
(** **** Aux *)
(* ----------------------------------------------------------------- *)

Lemma not__aname_sub_r_cname : forall (a : aname) (c : cname),
  ~ (|- TAName a << TCName c).
Proof.
  intros a c.
  remember (TAName a) as t1 eqn:Heq1. remember (TCName c) as t2 eqn:Heq2.
  intros Hcontra; induction Hcontra;
    try solve [inversion Heq1 | inversion Heq2].
  subst. tauto.
Qed.

Lemma not__aname_sub_r_pair : forall (a : aname) (t1 t2 : ty),
  ~ (|- TAName a << TPair t1 t2).
Proof.
  intros a t1 t2.
  remember (TAName a) as t eqn:Heq1. remember (TPair t1 t2) as t' eqn:Heq2.
  intros Hcontra; induction Hcontra;
    try solve [inversion Heq1 | inversion Heq2].
  subst. tauto.
Qed.

(*
Lemma aname_sub_r_union__aname_sub_r_component : forall (a : aname) (t1 t2 : ty),
    |- TAName a << TUnion t1 t2 ->
    |- TAName a << t1 \/ |- TAName a << t2.
Proof.
  intros a t1 t2.
  remember (TAName a) as t eqn:Heq1. remember (TUnion t1 t2) as t' eqn:Heq2.
  intros Hsub; induction Hsub;
    try solve [inversion Heq1 | inversion Heq2].
  - (* UnionR1 *)
    inversion Heq2; subst; tauto.
  - (* UnionR2 *)
    inversion Heq2; subst; tauto.
  - (* NF *)
    subst. simpl in IHHsub. tauto.
Qed.
*)

(* DEP: mk_nf_nf__equal, atomty_in_nf *)
Lemma atom_sub_r_union__atom_sub_r_component : forall (t t1 t2 : ty),
    atom_type t ->
    |- t << TUnion t1 t2 ->
    |- t << t1 \/ |- t << t2.
Proof.
  intros t t1 t2 Hat.
  remember (TUnion t1 t2) as t' eqn:Heq2.
  intros Hsub; induction Hsub;
    try solve [inversion Heq1 | inversion Heq2].
  - (* UnionL *)
    inversion Hat.
  - (* UnionR1 *)
    inversion Heq2; subst; tauto.
  - (* UnionR2 *)
    inversion Heq2; subst; tauto.
  - (* NF *)
    rewrite mk_nf_nf__equal in IHHsub.
    apply IHHsub; try assumption.
    apply atomty_in_nf; assumption.
Qed.

(* DEP: mk_nf_nf__equal *)
Lemma not__atom_pair_sub_r_cname : forall (c : cname) (t1 t2 : ty),
  atom_type t1 -> atom_type t2 ->
  ~ (|- TPair t1 t2 << TCName c).
Proof.
  intros c t1 t2 Hat1 Hat2.
  remember (TCName c) as t eqn:Heq1. remember (TPair t1 t2) as t' eqn:Heq2.
  intros Hcontra; induction Hcontra;
    try solve [inversion Heq1 | inversion Heq2].
  (* MkNF *)
  subst. apply IHHcontra. reflexivity.
  apply mk_nf_nf__equal. constructor. constructor; assumption.
Qed.

(* DEP: mk_nf_nf__equal *)
Lemma not__atom_pair_sub_r_aname : forall (a : aname) (t1 t2 : ty),
  atom_type t1 -> atom_type t2 ->
  ~ (|- TPair t1 t2 << TAName a).
Proof.
  intros a t1 t2 Hat1 Hat2.
  remember (TAName a) as t eqn:Heq1. remember (TPair t1 t2) as t' eqn:Heq2.
  intros Hcontra; induction Hcontra;
    try solve [inversion Heq1 | inversion Heq2].
  (* MkNF *)
  subst. apply IHHcontra. reflexivity.
  apply mk_nf_nf__equal. constructor. constructor; assumption.
Qed.

(* DEP: mk_nf_nf__equal *)
Lemma atom_pair_sub_r_pair__sub_r_components : forall (ta1 ta2 t1 t2 : ty),
    atom_type ta1 -> atom_type ta2 ->
    |- TPair ta1 ta2 << TPair t1 t2 ->
    |- ta1 << t1 /\ |- ta2 << t2.
Proof.
  intros ta1 ta2 t1 t2 Hta1 Hta2.
  remember (TPair ta1 ta2) as t eqn:Heq1. remember (TPair t1 t2) as t' eqn:Heq2.
  intros Hsub; induction Hsub;
    try solve [inversion Heq1 | inversion Heq2].
  - (* Pair *) 
    inversion Heq1; inversion Heq2; subst; tauto.
  - (* NF *)
    subst. apply IHHsub; try reflexivity.
    apply mk_nf_nf__equal; repeat constructor; assumption.
Qed.

(* DEP: match_ty__dcdbl, match_ty__sub_r_sound, match_valty__sub_r_complete,
        not__aname_sub_r_cname, not__aname_sub_r_pair,
        atom_pair_sub_r_pair__sub_r_components,
        atom_sub_r_union__atom_sub_r_component *)
Lemma atom_sub_r__decidable : forall (t1 t2 : ty),
    atom_type t1 ->
    valid t2 ->
    Decidable.decidable (|- t1 << t2).
Proof.
  intros t1 t2 Hat1. generalize dependent t2.
  induction Hat1.
  - (* CName *)
    intros t2 HTY2. destruct (match_ty__dcdbl (TCName n) t2) as [Hm | Hm].
    + left. apply match_ty__sub_r_sound. constructor. assumption.
    + right; intros Hcontra.
      assert (Hcontra': |- (TCName n) <$ t2)
        by (apply match_valty__sub_r_complete; assumption || constructor).
      contradiction.
  - (* AName *)
    intros t2; induction t2; intros HTY2.
    + (* CName *)
      right. apply not__aname_sub_r_cname.
    + (* AName *)
      destruct n; destruct a;
        try solve [left; (apply sub_r__rflxv; constructor) || constructor].
      right. intros Hcontra.
      remember (TAName NNum) as t1 eqn:Heq1. remember (TAName NReal) as t2 eqn:Heq2.
      induction Hcontra;
        try solve [inversion Heq1 | inversion Heq2].
      inversion Heq1; inversion Heq2; subst.
      inversion H1. subst. tauto.
    + (* Pair *)
      right. apply not__aname_sub_r_pair.
    + (* Union *)
      inversion HTY2; subst.
      destruct (IHt2_1 H1) as [IH1 | IH1];
        destruct (IHt2_2 H2) as [IH2 | IH2];
        try solve [
              left; apply SR_UnionR1; tauto
            | left; apply SR_UnionR2; tauto ].
      right; intros Hcontra.
      apply atom_sub_r_union__atom_sub_r_component in Hcontra.
      tauto. constructor.
    + (* Ext *)
      inversion HTY2.
  - (* Pair *)
    intros t' HTYt'. induction t'.
    + (* CName *)
      right; apply not__atom_pair_sub_r_cname; assumption.
    + (* AName *)
      right; apply not__atom_pair_sub_r_aname; assumption.
    + (* Pair *)
      inversion HTYt'; subst.
      destruct (IHHat1_1 t'1 H1) as [IH1 | IH1];
        destruct (IHHat1_2 t'2 H2) as [IH2 | IH2];
        solve [
            left; constructor; assumption
          | right; intros Hcontra;
            apply atom_pair_sub_r_pair__sub_r_components in Hcontra;
            try assumption;
            destruct Hcontra as [Hsub1 Hsub2]; contradiction ].
    + (* Union *)
      inversion HTYt'; subst.
      destruct (IHt'1 H1) as [IH1 | IH1];
        destruct (IHt'2 H2) as [IH2 | IH2];
        try solve [
              left; apply SR_UnionR1; assumption
            | left; apply SR_UnionR2; assumption ].
      right; intros Hcontra.
      apply atom_sub_r_union__atom_sub_r_component in Hcontra.
      tauto. constructor; assumption.
    + (* Ext *)
      inversion HTYt'.
Qed.

(* ----------------------------------------------------------------- *)
(** **** Main Properties *)
(* ----------------------------------------------------------------- *)

(* DEP: atom_sub_r__decidable, union_sub_r__components_sub_r *)
Lemma nf_sub_r__decidable : forall (t1 t2 : ty),
    InNF(t1) ->
    valid t2 ->
    Decidable.decidable (|- t1 << t2).
Proof.
  intros t1 t2 Hnf1. generalize dependent t2.
  induction Hnf1.
  - (* Atom *)
    intros t2 HTY2.
    destruct (atom_sub_r__decidable ta t2 H HTY2) as [Hm | Hm].
    + left; assumption. 
    + right; assumption.
  - (* Union *)
    intros t' HTYt'.
    pose proof (nf__valid _ Hnf1_1) as HTY1. pose proof (nf__valid _ Hnf1_2) as HTY2.
    destruct (IHHnf1_1 t' HTYt') as [IH1 | IH1];
      destruct (IHHnf1_2 t' HTYt') as [IH2 | IH2];
      try solve [
            right; intros Hcontra;
            destruct (union_sub_r__components_sub_r _ _ _ HTY1 HTY2 Hcontra) as [Hsub1 Hsub2];
            contradiction ].
    left; constructor; assumption.
Qed.
