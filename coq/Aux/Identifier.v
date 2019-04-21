(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(* Mainly borrowed from Sofware Foundations, v.4 
   $Date: 2015-12-11 17:17:29 -0500 (Fri, 11 Dec 2015) $
 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 


(* ***************************************************************** *)
(** * Identifiers as wrappers of nats *)
(* ***************************************************************** *)
(* ***************************************************************** *)

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.

Require Import Coq.Structures.Orders.
Require Import Coq.Structures.OrdersAlt.
Require Import Coq.Structures.Equalities.
Require Import Coq.ZArith.ZArith.

Require Import Coq.MSets.MSets.
Require Import Coq.FSets.FMapAVL.


(* ################################################################# *)
(** ** Identifier Definitions  *)
(* ################################################################# *)

Inductive id : Type :=
  | Id : nat -> id.

Definition beq_id id1 id2 :=
  match id1,id2 with
    | Id n1, Id n2 => beq_nat n1 n2
  end.

(* ================================================================= *)
(** *** Properties of Identifiers *)
(* ================================================================= *)

Theorem beq_id_refl : forall id, true = beq_id id id.
Proof.
  intros [n]. simpl. rewrite <- beq_nat_refl.
  reflexivity.
Qed.

Theorem beq_id_true_iff : forall id1 id2 : id,
  beq_id id1 id2 = true <-> id1 = id2.
Proof.
   intros [n1] [n2].
   unfold beq_id. 
   rewrite beq_nat_true_iff.
   split.
   - (* -> *) intros H. rewrite H. reflexivity.
   - (* <- *) intros H. inversion H. reflexivity.
Qed.

Theorem beq_id_false_iff : forall x y : id,
  beq_id x y = false
  <-> x <> y.
Proof.
  intros x y. rewrite <- beq_id_true_iff.
  rewrite not_true_iff_false. reflexivity.
Qed.

Theorem false_beq_id : forall x y : id,
   x <> y
   -> beq_id x y = false.
Proof.
  intros x y. rewrite beq_id_false_iff.
  intros H. apply H.
Qed.

(* ----------------------------------------------------------------- *)
(** **** Reflecting Equality of Identifiers *)
(* ----------------------------------------------------------------- *)

(** It's convenient to use the reflection idioms.  
    We begin by proving a fundamental _reflection lemma_ relating 
    the equality proposition on [id]s 
    with the boolean function [beq_id]. *)

(** Use the proof of [beq_natP] in chapter [IndProp] as a template to
    prove the following: *)

Lemma beq_idP : forall x y, reflect (x = y) (beq_id x y).
Proof.
  intros x y. 
  apply iff_reflect. symmetry. apply beq_id_true_iff.
Qed.

(* ----------------------------------------------------------------- *)
(** **** Propositional Equality of Identifiers *)
(* ----------------------------------------------------------------- *)

Definition eq_id x y : Prop :=
  match x, y with
    Id n, Id m => eq_nat n m
  end.

Lemma eq_id_iff_eq_nat : forall n m,
    eq_id (Id n) (Id m) <-> eq_nat n m.
Proof.
  tauto.
Qed. 

Theorem eq_id_decide : forall x y, {eq_id x y} + {~ eq_id x y}.
Proof.
  intros [n] [m]. simpl.
  apply eq_nat_decide.
Qed.

Theorem eq_id_dec : forall (x y : id), {x = y} + {x <> y}.
Proof.
  intros [x] [y]. destruct (eq_nat_dec x y) as [H|H].
  - subst. left. reflexivity.
  - right. intros contra. inversion contra as [contra'].
    apply H in contra'. assumption.
Qed.
