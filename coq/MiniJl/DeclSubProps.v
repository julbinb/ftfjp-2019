(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(*    MiniJl:
        Decidable, Tag-Based Semantic Subtyping 
        for Nominal Types, Pairs, and Unions.  *)

(** * MiniJl: Propositions about Declarative Subtyping *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

Add LoadPath "../..". (* root directory of the repo *)

Require Import MiniJl.Aux.Identifier.

Require Import MiniJl.MiniJl.BaseDefs.
Require Import MiniJl.MiniJl.BaseProps.
Require Import MiniJl.MiniJl.MatchProps.

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.

Open  Scope btjm_scope.
Open  Scope btjnf_scope.
Close Scope btjr_scope.
Open  Scope btj_scope.

(* ################################################################# *)
(** ** Properties related to Matching *)
(* ################################################################# *)

(** If [v <$ t1] and [t1 << t2], then [v <$ t2]. *)
Lemma match_valty__transitive_on_sub_d : forall (t1 t2 : ty),
    |- t1 << t2 ->
    forall (v : ty),
      value_type v ->
      |- v <$ t1 ->
      |- v <$ t2.
Proof.
  intros t1 t2 Hsub. 
  induction Hsub; subst; intros v Hval Hm1;
    try solve [inversion Hm1; repeat constructor].
  - (* Refl *)
    assumption.
  - (* Trans *)
    auto.
  - (* Pair *)
    inversion Hm1; subst. inversion Hval; subst.
    constructor; [apply IHHsub1 | apply IHHsub2]; assumption. 
  - (* Union *)
    inversion Hm1; subst; [apply IHHsub1 | apply IHHsub2]; tauto.
  - (* UnionR1 *)
    apply MT_Union1; assumption.
  - (* UnionR2 *)
    apply MT_Union2; assumption.
  - (* Distr1 *)
    inversion Hm1; subst. inversion H2; subst.
    apply MT_Union1; constructor; assumption.
    apply MT_Union2; constructor; assumption.
  - (* Distr2 *)
    inversion Hm1; subst; inversion H3; subst;
      [ apply MT_Union1 | apply MT_Union2]; constructor; assumption.
Qed.

(* ================================================================= *)
(** *** Correctness of Subtyping with respect to Matching *)
(* ================================================================= *)

Theorem match_ty__sub_d_sound : forall (v t : ty),
    |- v <$ t ->
    |- v << t.
Proof.
  intros v t H; induction H;
    try solve [
          repeat constructor
        | (apply SD_Trans with treal; repeat constructor) ].
  (* Pair *)   constructor; assumption.
  (* Union1 *) apply union_right_1; assumption.
  (* Union2 *) apply union_right_2; assumption.
Qed.

(** [v << t] implies [v <$ t]. *)
(* DEP: match_valty__rflxv, match_valty__transitive_on_sub_d *)
Theorem match_valty__sub_d_complete : forall (v t : ty),
    |- v << t ->
    value_type v ->
    |- v <$ t.
Proof.
  intros v t H; induction H; subst; intros Hval;
    try solve [constructor | inversion Hval].
  - (* Refl *)
    apply match_valty__rflxv; assumption.
  - (* Trans *)
    specialize (IHsub_d1 Hval).
    apply match_valty__transitive_on_sub_d with t2; assumption.
  - (* Pair *)
    inversion Hval; subst. constructor; tauto.
  - (* UnionR1 *)
    apply MT_Union1. apply match_valty__rflxv; assumption.
  - (* UnionR2 *)
    apply MT_Union2. apply match_valty__rflxv; assumption.
  - (* Distr1 *)
    inversion Hval; subst. inversion H1.
  - (* Distr2 *)
    inversion Hval; subst. inversion H2.
Qed.


(* ################################################################# *)
(** ** Properties related to Normal Form *)
(* ################################################################# *)

(* ----------------------------------------------------------------- *)
(** **** Aux *)
(* ----------------------------------------------------------------- *)

(* DEP: union_sub_d__components_sub_d,
        unite_pairs_t_union, unite_pairs_union_t *)
Lemma unite_pairs__preserves_sub_d1 : forall (t1 t2 t1' t2' : ty),
    |- t1 << t1' ->
    |- t2 << t2' ->
    |- unite_pairs t1 t2 << TPair t1' t2'.
Proof.
  intros ta; induction ta; intros tb.
  - (* CName *)
    induction tb; intros ta' tb' Hsub1 Hsub2;
      try solve [simpl; constructor; assumption].
    destruct (union_sub_d__components_sub_d _ _ _ Hsub2) as [Hsub21 Hsub22].
    rewrite unite_pairs_t_union; try resolve_not_union.
    constructor; [apply IHtb1 | apply IHtb2]; assumption.
  - (* AName *)
    induction tb; intros ta' tb' Hsub1 Hsub2;
      try solve [simpl; constructor; assumption].
    destruct (union_sub_d__components_sub_d _ _ _ Hsub2) as [Hsub21 Hsub22].
    rewrite unite_pairs_t_union; try resolve_not_union.
    constructor; [apply IHtb1 | apply IHtb2]; assumption.
  - (* Pair *)
    induction tb; intros ta' tb' Hsub1 Hsub2;
      try solve [simpl; constructor; assumption].
    destruct (union_sub_d__components_sub_d _ _ _ Hsub2) as [Hsub21 Hsub22].
    rewrite unite_pairs_t_union; try resolve_not_union.
    constructor; [apply IHtb1 | apply IHtb2]; assumption.
  - (* Union *)
    intros ta' tb' Hsub1 Hsub2.
    apply union_sub_d__components_sub_d in Hsub1.
    destruct Hsub1 as [Hsub11 Hsub12].
    rewrite unite_pairs_union_t.
    constructor; [apply IHta1 | apply IHta2]; assumption.
Qed.

(* DEP: union_sub_d__components_sub_d,
        unite_pairs_t_union, unite_pairs_union_t *)
Lemma unite_pairs__preserves_sub_d2 : forall (t1' t2' t1 t2 : ty),
    |- t1 << t1' ->
    |- t2 << t2' ->
    |- TPair t1 t2 << unite_pairs t1' t2'.
Proof.
  intros ta'; induction ta'; intros tb'.
  - (* CName *)
    induction tb'; intros ta tb Hsub1 Hsub2;
      try solve [simpl; constructor; assumption].
    rewrite unite_pairs_t_union; try resolve_not_union.
    apply SD_Trans with (TPair ta (TUnion tb'1 tb'2)).
    + constructor; constructor || assumption.
    + apply SD_Trans with (TUnion (TPair ta tb'1) (TPair ta tb'2)).
      apply SD_Distr2. apply SD_UnionL.
      apply union_right_1; apply IHtb'1; assumption || constructor.
      apply union_right_2; apply IHtb'2; assumption || constructor.
  - (* AName *)
    induction tb'; intros ta tb Hsub1 Hsub2;
      try solve [simpl; constructor; assumption].
    rewrite unite_pairs_t_union; try resolve_not_union.
    apply SD_Trans with (TPair ta (TUnion tb'1 tb'2)).
    + constructor; constructor || assumption.
    + apply SD_Trans with (TUnion (TPair ta tb'1) (TPair ta tb'2)).
      apply SD_Distr2. apply SD_UnionL.
      apply union_right_1; apply IHtb'1; assumption || constructor.
      apply union_right_2; apply IHtb'2; assumption || constructor.
  - (* Pair *)
    induction tb'; intros ta tb Hsub1 Hsub2;
      try solve [simpl; constructor; assumption].
    rewrite unite_pairs_t_union; try resolve_not_union.
    apply SD_Trans with (TPair ta (TUnion tb'1 tb'2)).
    + constructor; constructor || assumption.
    + apply SD_Trans with (TUnion (TPair ta tb'1) (TPair ta tb'2)).
      apply SD_Distr2. apply SD_UnionL.
      apply union_right_1; apply IHtb'1; assumption || constructor.
      apply union_right_2; apply IHtb'2; assumption || constructor.
  - (* Union *)
    intros ta tb Hsub1 Hsub2.
    rewrite unite_pairs_union_t.
    apply SD_Trans with (TPair (TUnion ta'1 ta'2) tb).
    + constructor; constructor || assumption.
    + apply SD_Trans with (TUnion (TPair ta'1 tb) (TPair ta'2 tb)).
      apply SD_Distr1. apply SD_UnionL.
      apply union_right_1; apply IHta'1; assumption || constructor.
      apply union_right_2; apply IHta'2; assumption || constructor.
Qed.

(* ----------------------------------------------------------------- *)
(** **** Main Properties *)
(* ----------------------------------------------------------------- *)

(* DEP: unite_pairs__preserves_sub_d1 *)
Lemma mk_nf__sub_d1 : forall (t : ty),
    |- MkNF(t) << t.
Proof.
  induction t.
  - (* CName *)
    simpl; constructor.
  - (* AName *)
    destruct a; simpl; repeat constructor;
      apply SD_Trans with treal; constructor.
  - (* Pair *)
    simpl. apply unite_pairs__preserves_sub_d1; assumption.
  - (* Union *)
    simpl; constructor;
      [apply union_right_1 | apply union_right_2]; assumption.
Qed.

(* DEP: unite_pairs__preserves_sub_d3 *)
Lemma mk_nf__sub_d2 : forall (t : ty),
    |- t << MkNF(t).
Proof.
  induction t.
  - (* CName *)
    simpl; constructor.
  - (* AName *)
    destruct a; simpl; try constructor.
    apply SD_Trans with (TUnion treal tcmplx); repeat constructor.
    apply union_right_1; constructor.
  - (* Pair *)
    simpl. apply unite_pairs__preserves_sub_d2; assumption.
  - (* Union *)
    simpl. constructor.
    apply union_right_1; assumption.
    apply union_right_2; assumption.
Qed.

(** Exists a declaratively equivalent type in normal form. *)
(* DEP: mk_nf__in_nf, mk_nf__sub_d1, mk_nf__sub_d2 *)
Theorem nf_exists : forall (t : ty),
    exists (tn : ty),
      InNF(tn) /\
      |- tn << t /\ |- t << tn.
Proof.
  intros t. exists (MkNF(t)).
  repeat split.
  apply mk_nf__in_nf.
  apply mk_nf__sub_d1.
  apply mk_nf__sub_d2.
Qed.

(** If [InNF(t)], then [[t] <= [t']] implies [t << t']. *)
(* DEP: match_ty__sub_d_sound, match_valty__rflxv *)
Theorem nf_sem_sub__sub_d : forall (t : ty),
    InNF(t) ->
    forall (t' : ty),
      ||- [t] <= [t'] ->
      |- t << t'.
Proof.
  intros t Hnf; induction Hnf; intros t' Hval; unfold sem_sub.
  - (* Value *)
    apply match_ty__sub_d_sound. apply Hval.
    assumption. apply match_valty__rflxv. assumption.
  - (* Union *)
    constructor; [apply IHHnf1 | apply IHHnf2]; intros v Hv Hsub;
      try assumption; apply Hval; try assumption.
    apply MT_Union1; assumption.
    apply MT_Union2; assumption.
Qed.

