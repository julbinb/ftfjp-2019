(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(*    FullAtomicJl:
        Decidable, Tag-Based Semantic Subtyping 
        for Nominal Types, Pairs, and Unions.  *)

(** * FullAtomicJl: Propositions about Semantic Subtyping *)
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

Open  Scope btjm_scope.

(* ################################################################# *)
(** ** Basic Properties *)
(* ################################################################# *)

Theorem sem_sub__reflexive : forall (t : ty),
    ||- [t] <= [t].
Proof.
  auto.
Qed.

Lemma sem_sub_pair : forall (t1 t2 t1' t2' : ty),
    ||- [t1] <= [t1'] ->
    ||- [t2] <= [t2'] ->
    ||- [TPair t1 t2] <= [TPair t1' t2'].
Proof.
  intros t1 t2 t1' t2'. unfold sem_sub.
  intros Hsub1 Hsub2.
  intros v Hv Hm.
  inversion Hm; subst. inversion Hv; subst.
  constructor; [apply Hsub1 | apply Hsub2]; assumption.
Qed.

Lemma sem_sub_union1 : forall (t t1' t2' : ty),
    ||- [t] <= [t1'] ->
    ||- [t] <= [TUnion t1' t2'].
Proof.
  intros t t1' t2'. unfold sem_sub.
  intros Hsub. intros v Hv Hm.
  apply MT_Union1; apply Hsub; assumption.
Qed.

Lemma sem_sub_union2 : forall (t t1' t2' : ty),
    ||- [t] <= [t2'] ->
    ||- [t] <= [TUnion t1' t2'].
Proof.
  intros t t1' t2'. unfold sem_sub.
  intros Hsub. intros v Hv Hm.
  apply MT_Union2; apply Hsub; assumption.
Qed.

Lemma real_sem_sub_num :
  ||- [treal] <= [tnum].
Proof.
  unfold sem_sub.
  intros v Hv; induction Hv; intros Hm;
    try solve [inversion Hm | constructor].
  destruct cn; constructor || inversion Hm.
  destruct an; constructor || inversion Hm.
Qed.

(* ################################################################# *)
(** ** Relation to Matching *)
(* ################################################################# *)

(** Semantic subtyping of a value type amounts
    to a single matching *)
(* DEP: sem_sub__reflexive, sem_sub_pair,
        match_ty__value_type, valty_match_valty__equal *)
Lemma match_ty__sem_sub : forall (v t : ty),
    |- v <$ t ->
    ||- [v] <= [t].
Proof.
  intros v t Hm; induction Hm;
    try solve [
          apply sem_sub__reflexive
        | intros v Hv Hm; inversion Hm; subst; constructor ].
  - (* Pair *)
    apply sem_sub_pair; assumption.
  - (* UnionR1 *)
    intros v Hv Hvm.
    pose proof (match_ty__value_type _ _ Hm) as Hval.
    pose proof (valty_match_valty__equal _ _ Hvm Hval) as Heq.
    subst. apply MT_Union1; assumption.
  - (* UnionR2 *)
    intros v Hv Hvm.
    pose proof (match_ty__value_type _ _ Hm) as Hval.
    pose proof (valty_match_valty__equal _ _ Hvm Hval) as Heq.
    subst. apply MT_Union2; assumption.
Qed.

Lemma valty_sem_sub__match_ty : forall (v t : ty),
    value_type v ->
    ||- [v] <= [t] ->
    |- v <$ t.
Proof.
  intros v t Hv Hsem.
  apply Hsem. assumption.
  apply match_valty__rflxv; assumption.
Qed.

(* ################################################################# *)
(** ** Properties of Extension Types *)
(* ################################################################# *)

(** We need to show that atomic types cannot be splitted 
    into valid unions because of thei extension subtypes. *)

(* ----------------------------------------------------------------- *)
(** **** Aux *)
(* ----------------------------------------------------------------- *)

(* DEP: sem_sub__reflexive, real_sem_sub_num *)
Lemma ext_match__aname_sem_sub : forall (an : aname) (t' : ty),
    valid t' ->
    |- TExt an <$ t' ->
    ||- [TAName an] <= [t'].
Proof.
  intros an t' HTYt' Hmtch.
  remember (TExt an) as t eqn:Heqt.
  induction Hmtch;
    try solve [ inversion Heqt | inversion HTYt' ];
    inversion Heqt; subst;
      try apply sem_sub__reflexive.
  - (* Real <= Num *)
   apply real_sem_sub_num.
  - (* UnionR1 *)
    inversion HTYt'; subst.
    specialize (IHHmtch H2 H).
    unfold sem_sub in *. auto.
  - (* UnionR2 *)
    inversion HTYt'; subst.
    specialize (IHHmtch H3 H).
    unfold sem_sub in *. auto.
Qed.

(** [ext_type] means that a (value) type contains
    an extension type. *)
Inductive ext_type : ty -> Prop :=
| ET_Ext   : forall (an : aname),
    ext_type (TExt an)
| ET_Pair1 : forall (t1 t2 : ty),
    ext_type t1 ->
    ext_type (TPair t1 t2)
| ET_Pair2 : forall (t1 t2 : ty),
    ext_type t2 ->
    ext_type (TPair t1 t2)
.

(** [ext_bound v] returns an atomic type that
    is the least supertype of an ext-value-type [v]. *)
Fixpoint ext_bound (v : ty) :=
  match v with
  | TExt an     => TAName an
  | TPair v1 v2 => TPair (ext_bound v1) (ext_bound v2)
  | _           => v
  end.

(** If a value type does not contain extension types,
    its bound is itself. *)
Lemma value_type__ext_bound : forall (v : ty),
    value_type v ->
    ext_type v  \/  ext_bound v = v.
Proof.
  intros v Hv; induction Hv; simpl.
  - (* CName *)
    right; reflexivity.
  - (* Pair *)
    destruct IHHv1 as [H1 | H1]; destruct IHHv2 as [H2 | H2];
      try solve [ left; apply ET_Pair1; assumption
                | left; apply ET_Pair2; assumption].
    right; rewrite H1; rewrite H2; reflexivity.
  - (* Ext *)
    left; constructor.
Qed.

Lemma atom_type__ext_bound_equal : forall (t : ty),
    atom_type t ->
    ext_bound t = t.
Proof.
  intros t Hat; induction Hat; simpl;
    try reflexivity.
  (* Pair *)
  rewrite IHHat1; rewrite IHHat2; reflexivity.
Qed.

(** If an ext-value type matches a type, 
    the ext-bound of the value type is a semantic subtype
    of that type, because an ext-type matches
    only a corresponding abstract type.  *)
(* DEP: sem_sub__reflexive, real_sem_sub_num,
        match_ty__value_type, value_type__ext_bound,
        match_ty__sem_sub, sem_sub_union1/2 *)
Lemma ext_type_match__ext_bound_sem_sub : forall (v t' : ty),
    |- v <$ t' ->
    ext_type v ->
    valid t' ->
    ||- [ext_bound v] <= [t'].
Proof.
  intros v t' Hm.
  induction Hm; intros Hext HTYt';
    try solve [inversion Hext | inversion HTYt']; simpl.
  + (* AName <= AName *)
    apply sem_sub__reflexive.
  + (* Real <= Num *)
    apply real_sem_sub_num.
  + (* Pair *)
    inversion HTYt'; subst.
    pose proof (match_ty__value_type _ _ Hm1) as Hv1.
    pose proof (match_ty__value_type _ _ Hm2) as Hv2.
    pose proof (value_type__ext_bound _ Hv1) as Ht1.
    pose proof (value_type__ext_bound _ Hv2) as Ht2.
    apply sem_sub_pair.
    * destruct Ht1 as [Ht1 | Ht1].
      apply IHHm1; assumption.
      rewrite Ht1; apply match_ty__sem_sub; assumption.
    * destruct Ht2 as [Ht2 | Ht2].
      apply IHHm2; assumption.
      rewrite Ht2; apply match_ty__sem_sub; assumption.
  + (* Union1 *)
    inversion HTYt'; subst.
    apply sem_sub_union1; apply IHHm; assumption.
  + (* Union2 *)
    inversion HTYt'; subst.
    apply sem_sub_union2; apply IHHm; assumption.
Qed.

(** Each atom type is either a value type,
    or there exists an ext-value subtype of it. *)
(* DEP: match_valty__rflxv, 
        atom_type__ext_bound_equal *)
Lemma atom_type__value_type_or_exists_matching_ext : forall (t : ty),
    atom_type t ->
    value_type t
    \/
    exists (v : ty), |- v <$ t /\ ext_type v /\ ext_bound v = t.
Proof.
  intros t Hat; induction Hat.
  - (* CName *)
    left; constructor. 
  - (* AName *)
    right; exists (TExt n). split; repeat constructor.
  - (* Pair *)
    destruct IHHat1 as [Hv1 | [v1 [Hm1 [He1 Hb1]]]];
      destruct IHHat2 as [Hv2 | [v2 [Hm2 [He2 Hb2]]]].
    + left; constructor; assumption.
    + right; exists (TPair ta1 v2); split.
      constructor; apply match_valty__rflxv || assumption; assumption.
      split. apply ET_Pair2; assumption.
      simpl. rewrite Hb2. rewrite (atom_type__ext_bound_equal _ Hat1).
      reflexivity.
    + right; exists (TPair v1 ta2); split.
      constructor; apply match_valty__rflxv || assumption; assumption.
      split. apply ET_Pair1; assumption.
      simpl. rewrite Hb1. rewrite (atom_type__ext_bound_equal _ Hat2).
      reflexivity.
    + right; exists (TPair v1 v2); split.
      constructor; assumption. split.
      constructor; assumption.
      simpl; rewrite Hb1; rewrite Hb2; reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(** **** Main Properties *)
(* ----------------------------------------------------------------- *)

(* DEP: ext_match__aname_sem_sub *)
Lemma aname_sem_sub_valid_union__aname_sem_sub_component :
  forall (an : aname) (ta tb : ty),
    valid ta -> valid tb ->
    ||- [TAName an] <= [TUnion ta tb] ->
    ||- [TAName an] <= [ta] \/ ||- [TAName an] <= [tb].
Proof.
  intros an ta tb HTYta HTYtb H.
  assert (Hv: value_type (TExt an)) by constructor.
  assert (Hm: |- TExt an <$ TAName an) by constructor.
  specialize (H _ Hv Hm).
  inversion H; subst; [left | right];
    apply ext_match__aname_sem_sub; assumption.
Qed.

(* DEP: matching_valty__exists, match_ty__value_type,
        atom_type__value_type_or_exists_matching_ext,
        match_valty__rflxv, match_ty__sem_sub,
        ext_type_match__ext_bound_sem_sub *)
Lemma atom_pair_sem_sub_valid_union__atom_pair_sem_sub_component :
  forall (t1 t2 : ty),
    atom_type t1 -> atom_type t2 ->
    forall (ta tb : ty),
    valid ta -> valid tb ->
    ||- [TPair t1 t2] <= [TUnion ta tb] ->
    ||- [TPair t1 t2] <= [ta] \/ ||- [TPair t1 t2] <= [tb].
Proof.
  intros t1 t2 Hat1 Hat2.
  intros ta tb HTYa HTYb Hval.
  destruct (matching_valty__exists (TPair t1 t2)) as [v [Hv Hsub]].
  inversion Hsub; subst.
  assert (Hat: atom_type (TPair t1 t2)) by (constructor; assumption).
  destruct (atom_type__value_type_or_exists_matching_ext _ Hat)
    as [Hpv | [pv [Hpm [Hpe Hpb]]]].
  - inversion Hpv; subst.
    assert (Hpm: |- TPair t1 t2 <$ TPair t1 t2)
      by (apply match_valty__rflxv; assumption).
    specialize (Hval _ Hpv Hpm).
    inversion Hval; subst;
      [left | right]; apply match_ty__sem_sub; assumption.
  - pose proof (match_ty__value_type _ _ Hpm) as Hpv.
    specialize (Hval _ Hpv Hpm). rewrite <- Hpb.
    inversion Hval; subst; [left | right];
      apply ext_type_match__ext_bound_sem_sub; assumption.
Qed.