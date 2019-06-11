(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(*    FullAtomicJl:
        Decidable, Tag-Based Semantic Subtyping 
        for Nominal Types, Pairs, and Unions.  *)

(** * FullAtomicJl: Propositions about Declarative Subtyping *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

Add LoadPath "../..". (* root directory of the repo *)

Require Import Mechanization.Aux.Identifier.

Require Import Mechanization.FullAtomicJl.BaseDefs.
Require Import Mechanization.FullAtomicJl.BaseProps.
Require Import Mechanization.FullAtomicJl.MatchProps.
Require Import Mechanization.FullAtomicJl.SemSubProps.

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.

Open  Scope btjm_scope.
Open  Scope btjnf_scope.
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
    try solve [inversion Hm1; constructor].
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

(** [v <$ t] implies [v << t] *)
Theorem match_ty__sub_d_sound : forall (v t : ty),
    valid v ->
    |- v <$ t ->
    |- v << t.
Proof.
  intros v t HTYv H; induction H;
    try solve [
          repeat constructor
        | (apply SD_Trans with treal; repeat constructor)
        | inversion HTYv ].
  (* Pair *)   inversion HTYv; subst; constructor; tauto.
  (* Union1 *) apply union_right_1; tauto.
  (* Union2 *) apply union_right_2; tauto.
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
    valid t1 ->
    |- t1 << t1' ->
    |- t2 << t2' ->
    |- unite_pairs t1 t2 << TPair t1' t2'.
Proof.
  intros ta; induction ta; intros tb.
  - (* CName *)
    induction tb; intros ta' tb' HTYa Hsub1 Hsub2;
      try solve [simpl; constructor; assumption].
    destruct (union_sub_d__components_sub_d _ _ _ Hsub2) as [Hsub21 Hsub22].
    rewrite unite_pairs_t_union; try resolve_not_union.
    constructor; [apply IHtb1 | apply IHtb2]; assumption.
  - (* AName *)
    induction tb; intros ta' tb' HTYa Hsub1 Hsub2;
      try solve [simpl; constructor; assumption].
    destruct (union_sub_d__components_sub_d _ _ _ Hsub2) as [Hsub21 Hsub22].
    rewrite unite_pairs_t_union; try resolve_not_union.
    constructor; [apply IHtb1 | apply IHtb2]; assumption.
  - (* Pair *)
    induction tb; intros ta' tb' HTYa Hsub1 Hsub2;
      try solve [simpl; constructor; assumption].
    destruct (union_sub_d__components_sub_d _ _ _ Hsub2) as [Hsub21 Hsub22].
    rewrite unite_pairs_t_union; try resolve_not_union.
    constructor; [apply IHtb1 | apply IHtb2]; assumption.
  - (* Union *)
    intros ta' tb' HTYa Hsub1 Hsub2.
    apply union_sub_d__components_sub_d in Hsub1.
    destruct Hsub1 as [Hsub11 Hsub12].
    rewrite unite_pairs_union_t.
    inversion HTYa; subst.
    constructor; [apply IHta1 | apply IHta2]; assumption.
  - (* Ext *)
    intros ta' tb' HTYa; inversion HTYa.
Qed.

(* DEP: union_sub_d__components_sub_d,
        unite_pairs_t_union, unite_pairs_union_t *)
Lemma unite_pairs__preserves_sub_d2 : forall (t1' t2' t1 t2 : ty),
    valid t1' ->
    |- t1 << t1' ->
    |- t2 << t2' ->
    |- TPair t1 t2 << unite_pairs t1' t2'.
Proof.
  intros ta'; induction ta'; intros tb'.
  - (* CName *)
    induction tb'; intros ta tb HTYa' Hsub1 Hsub2;
      try solve [simpl; constructor; assumption].
    rewrite unite_pairs_t_union; try resolve_not_union.
    apply SD_Trans with (TPair ta (TUnion tb'1 tb'2)).
    + constructor; constructor || assumption.
    + apply SD_Trans with (TUnion (TPair ta tb'1) (TPair ta tb'2)).
      apply SD_Distr2. apply SD_UnionL.
      apply union_right_1; apply IHtb'1; assumption || constructor.
      apply union_right_2; apply IHtb'2; assumption || constructor.
  - (* AName *)
    induction tb'; intros ta tb HTYa' Hsub1 Hsub2;
      try solve [simpl; constructor; assumption].
    rewrite unite_pairs_t_union; try resolve_not_union.
    apply SD_Trans with (TPair ta (TUnion tb'1 tb'2)).
    + constructor; constructor || assumption.
    + apply SD_Trans with (TUnion (TPair ta tb'1) (TPair ta tb'2)).
      apply SD_Distr2. apply SD_UnionL.
      apply union_right_1; apply IHtb'1; assumption || constructor.
      apply union_right_2; apply IHtb'2; assumption || constructor.
  - (* Pair *)
    induction tb'; intros ta tb HTYa' Hsub1 Hsub2;
      try solve [simpl; constructor; assumption].
    rewrite unite_pairs_t_union; try resolve_not_union.
    apply SD_Trans with (TPair ta (TUnion tb'1 tb'2)).
    + constructor; constructor || assumption.
    + apply SD_Trans with (TUnion (TPair ta tb'1) (TPair ta tb'2)).
      apply SD_Distr2. apply SD_UnionL.
      apply union_right_1; apply IHtb'1; assumption || constructor.
      apply union_right_2; apply IHtb'2; assumption || constructor.
  - (* Union *)
    intros ta tb HTYa' Hsub1 Hsub2.
    rewrite unite_pairs_union_t.
    inversion HTYa'; subst.
    apply SD_Trans with (TPair (TUnion ta'1 ta'2) tb).
    + constructor; constructor || assumption.
    + apply SD_Trans with (TUnion (TPair ta'1 tb) (TPair ta'2 tb)).
      apply SD_Distr1. apply SD_UnionL.
      apply union_right_1; apply IHta'1; assumption || constructor.
      apply union_right_2; apply IHta'2; assumption || constructor.
  - (* Ext *)
    intros ta tb HTYa'; inversion HTYa'.
Qed.

(* ----------------------------------------------------------------- *)
(** **** Main Properties *)
(* ----------------------------------------------------------------- *)

(* DEP: unite_pairs__preserves_sub_d1 *)
Lemma mk_nf__sub_d1 : forall (t : ty),
    valid t ->
    |- MkNF(t) << t.
Proof.
  intros t HTYt; induction HTYt.
  - (* CName *)
    simpl; constructor.
  - (* AName *)
    destruct an; simpl; repeat constructor;
      apply SD_Trans with treal; constructor.
  - (* Pair *)
    simpl. pose proof (mk_nf__preserves_valid _ HTYt1) as H1.
    pose proof (mk_nf__preserves_valid _ HTYt2) as H2.
    apply unite_pairs__preserves_sub_d1; assumption.
  - (* Union *)
    simpl; constructor;
      [apply union_right_1 | apply union_right_2]; assumption.
Qed.

(* DEP: unite_pairs__preserves_sub_d3 *)
Lemma mk_nf__sub_d2 : forall (t : ty),
    valid t ->
    |- t << MkNF(t).
Proof.
  intros t HTYt; induction HTYt.
  - (* CName *)
    simpl; constructor.
  - (* AName *)
    destruct an; simpl; try constructor.
  - (* Pair *)
    simpl. pose proof (mk_nf__preserves_valid _ HTYt1) as H1.
    pose proof (mk_nf__preserves_valid _ HTYt2) as H2.
    apply unite_pairs__preserves_sub_d2; assumption.
  - (* Union *)
    simpl. constructor.
    apply union_right_1; assumption.
    apply union_right_2; assumption.
Qed.

(** Exists a declaratively equivalent type in normal form. *)
(* DEP: mk_nf__in_nf, mk_nf__sub_d1, mk_nf__sub_d2 *)
Theorem nf_exists : forall (t : ty),
    valid t ->
    exists (tn : ty),
      InNF(tn) /\
      |- tn << t /\ |- t << tn.
Proof.
  intros t HTYt. exists (MkNF(t)).
  repeat split.
  apply mk_nf__in_nf; assumption.
  apply mk_nf__sub_d1; assumption.
  apply mk_nf__sub_d2; assumption.
Qed.
 

(* ################################################################# *)
(** ** Relation to Semantic Subtyping *)
(* ################################################################# *)

(* ----------------------------------------------------------------- *)
(** **** Aux *)
(* ----------------------------------------------------------------- *)

(* DEP: match_ty__sub_d_sound,
        aname_sem_sub_valid_union__aname_sem_sub_component,
        matching_valpair__exists, matching_valty__exists,
        atom_pair_sem_sub_valid_union__atom_pair_sem_sub_component *)
Lemma atom_sem_sub__sub_d : forall (t : ty),
    atom_type t ->
    forall (t' : ty),
      valid t' ->
      ||- [t] <= [t'] ->
      |- t << t'.
Proof.
  intros t Hat; induction Hat; intros t' HTYt' Hval; unfold sem_sub.
  - (* CName *)
    unfold sem_sub in Hval.
    apply match_ty__sub_d_sound; try constructor.
    apply Hval; constructor.
  - (* AName *)
    unfold sem_sub in Hval.
    induction HTYt'.
    + (* CName *)
      assert (Hcontra: |- TExt n <$ TCName cn)
        by (apply Hval; constructor).
      inversion Hcontra.
    + (* AName *)
      destruct n; destruct an; subst; try apply SD_Refl.
      constructor.
      assert (Hcontra: |- TCName NCmplx <$ TAName NReal)
        by (apply Hval; constructor).
      inversion Hcontra.
    + (* Pair *)
      destruct n;
      assert (Hcontra: |- TCName NInt <$ TPair t1 t2)
        by (apply Hval; constructor);
      inversion Hcontra.
    + (* Union *)
      (* We need to prove that either all v match t1 or all v match t2 *)
      pose proof (aname_sem_sub_valid_union__aname_sem_sub_component _ _ _ HTYt'1 HTYt'2 Hval) as H.
      destruct H as [H | H];
        [ (apply union_right_1; apply IHHTYt'1)
        | (apply union_right_2; apply IHHTYt'2)];
        assumption.
  - (* Pair *)
    induction HTYt'.
    + (* CName *)
      destruct (matching_valpair__exists ta1 ta2) as [v1 [v2 [Hpv Hpm]]].
      specialize (Hval _ Hpv Hpm). inversion Hval.
    + (* AName *)
      destruct (matching_valpair__exists ta1 ta2) as [v1 [v2 [Hpv Hpm]]].
      specialize (Hval _ Hpv Hpm). inversion Hval.
    + (* Pair *)
      unfold sem_sub in Hval.
      constructor; [apply IHHat1 | apply IHHat2];
        try assumption; unfold sem_sub; intros v Hv Hm.
      * destruct (matching_valty__exists ta2) as [v' [Hv' Hm']].
        assert (Hpv: value_type (TPair v v')) by (constructor; assumption).
        assert (Hpm: |- TPair v v' <$ TPair ta1 ta2) by (constructor; assumption).
        specialize (Hval _ Hpv Hpm). inversion Hval; subst.
        assumption.
      * destruct (matching_valty__exists ta1) as [v' [Hv' Hm']].
        assert (Hpv: value_type (TPair v' v)) by (constructor; assumption).
        assert (Hpm: |- TPair v' v <$ TPair ta1 ta2) by (constructor; assumption).
        specialize (Hval _ Hpv Hpm). inversion Hval; subst.
        assumption.
    + (* Union *)
      destruct (atom_pair_sem_sub_valid_union__atom_pair_sem_sub_component _ _ Hat1 Hat2 _ _ HTYt'1 HTYt'2 Hval).
      apply union_right_1; apply IHHTYt'1; assumption.
      apply union_right_2; apply IHHTYt'2; assumption.
Qed.

(* ----------------------------------------------------------------- *)
(** **** Main Properties *)
(* ----------------------------------------------------------------- *)

(** If [InNF(t)] and [valid t'], then [[t] <= [t']] implies [t << t']. *)
(* DEP: atom_sem_sub__sub_d *)
Theorem nf_sem_sub__sub_d : forall (t : ty),
    InNF(t) ->
    forall (t' : ty),
      valid t' ->
      ||- [t] <= [t'] ->
      |- t << t'.
Proof.
  intros t Hnf; induction Hnf; intros t' HTYt' Hval; unfold sem_sub.
  - (* Atom *)
    apply atom_sem_sub__sub_d; assumption.
  - (* Union *)
    constructor; [apply IHHnf1 | apply IHHnf2];
      try assumption;
      intros v Hv Hsub;
      try assumption; apply Hval; try assumption;
      [apply MT_Union1 | apply MT_Union2]; assumption.
Qed.

(* ################################################################# *)
(** ** Validity *)
(* ################################################################# *)

Lemma sub_d__valid1 : forall (t1 t2 : ty),
    |- t1 << t2 ->
    valid t2 ->
    valid t1.
Proof.
  intros t1 t2 Hsub; induction Hsub; intros HTY2;
    try solve [ tauto
        | constructor; tauto].
  - (* Pair *)
    inversion HTY2; subst.
    constructor; tauto.
  - (* Union1 *)
    inversion HTY2; subst; tauto.
  - (* Union2 *)
    inversion HTY2; subst; tauto.
  - (* Distr1 *)
    inversion HTY2; subst.
    inversion H1; inversion H2; subst.
    repeat constructor; tauto.
  - (* Distr2 *)
    inversion HTY2; subst.
    inversion H1; inversion H2; subst.
    repeat constructor; tauto.
Qed.