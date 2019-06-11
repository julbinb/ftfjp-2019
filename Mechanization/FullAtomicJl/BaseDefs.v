(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *) 
(*    FullAtomicJl:
        Decidable, Tag-Based Semantic Subtyping 
        for Nominal Types, Pairs, and Unions.  *)

(** * FullAtomicJl: Definitions *)
(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

Add LoadPath "../..". (* root directory of the repo *)

Require Import  Mechanization.Aux.Identifier.

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.

(** Our goal is to define "semantic" subtyping on 
    nominal types, covariant pairs, and unions.
    We are going to interpret types as sets of type tags
    (i.e. types that have direct instances). 
    When interpreting abstract nominal types, we also account for 
    their future subtypes.
 *)

(* ################################################################# *)
(** ** Types *)
(* ################################################################# *)

(** We start with the full grammar of types:

    [τ ::= cname | aname | τ1×τ2 | τ1∪τ2 | Ext<aname> ]

    where [cname] is a _concrete_ nominal (named) type, 
    that is a type of a user-defined/built-in value,
    [aname] is an _abstract_ nominal type,
    and [Ext<aname>] is an extension type, 
    i.e. "future" concrete nominal subtype of 
    an abstract nominal type.
    Extension types cannot be used by the user.
 *)

(*
  τ,σ ::= 
        | Int | Flt 
        | Real 
        | Cmplx 
        | Num
        | Str 
        | τ1×τ2
        | τ1∪τ2
        | E_Real
        | E_Num
*)

(** Concrete nominal type *)
Inductive cname : Type := NInt | NFlt | NCmplx | NStr.

(** Abstract nominal type *)
Inductive aname : Type := NReal | NNum.

(** MiniJl type *)
Inductive ty : Type :=
| TCName : cname -> ty                    (* concrete type *)
| TAName : aname -> ty                    (* abstract type *)
| TPair  : ty -> ty -> ty                 (* ty1×ty2, covariant pair *)
| TUnion : ty -> ty -> ty                 (* ty1∪ty2, union type *)
| TExt   : aname -> ty                    (* Ext<an>, extension type *)
.

(* ================================================================= *)
(** *** Valid types *)
(* ================================================================= *)

(** Extension types are only for defining semantic subtyping, 
    they are not considered "valid" types. *)

Inductive valid : ty -> Prop :=
| TY_CName : forall (cn : cname),
    valid (TCName cn)
| TY_AName : forall (an : aname),
    valid (TAName an)
| TY_Pair : forall (t1 t2 : ty),
    valid t1 -> valid t2 ->
    valid (TPair t1 t2)
| TY_Union : forall (t1 t2 : ty),
    valid t1 -> valid t2 ->
    valid (TUnion t1 t2)
.

(* ================================================================= *)
(** *** Examples *)
(* ================================================================= *)

Definition tint   := TCName NInt.
Definition tflt   := TCName NFlt.
Definition tcmplx := TCName NCmplx.
Definition tstr   := TCName NStr.

Definition treal  := TAName NReal.
Definition tnum   := TAName NNum.

Definition tIntInt := TPair (TCName NInt) (TCName NInt).
Definition tNumNum := TPair (TAName NNum) (TAName NNum).


(* ################################################################# *)
(** ** Value Types *)
(* ################################################################# *)

(** Types such as [Str] ([cname]), [Flt×Flt] ([cname×cname]),
    or [Int×(Flt×Flt)] we call _value types_ because they represent
    type tags of run-time values.
    Value types are either concrete named types 
    or pairs of value types
    or extension types, as they represent potential values.

    Note that types such as [Int∪Int] are not value types, 
    though [Int∪Int] should be equivalent to a value type [Int]. 

    We will denote value types with [v].
 *)

(** Value type (type tag that can be instantiated) *)
Inductive value_type : ty -> Prop :=
| VT_CName : forall (cn : cname),
    value_type (TCName cn)
| VT_Pair  : forall (v1 v2 : ty),
    value_type v1 ->
    value_type v2 ->
    value_type (TPair v1 v2)
| VT_Ext : forall (an : aname),
    value_type (TExt an)
.                      

Hint Constructors value_type.


(* ################################################################# *)
(** ** Matching Relation *)
(* ################################################################# *)

(** As we consider all values to be tagged with value types,
    we interpret types as sets of value types:
    
        [[τ]] = 2^V where V is the set of value types.
    
    Namely:
      
        [[cname]] = {cname}
        [[real]]  = {int, flt, Ext<real>}
        [[num]]   = {int, flt, cmplx, Ext<real>, Ext<num>}
        [[τ1×τ2]] = [[τ1]] × [[τ2]]
        [[τ1∪τ2]] = [[τ1]] ∪ [[τ2]]
    
    Note that extension types are used in the interpretation 
    of abstract nominal types.
    
    Below, we define a _matching relation_ [⊢ v <$ τ],
    which is equivalent to [v \in [[τ]]].
 *)

(*
  ----------------------- MT-CName
   ⊢ CName c <$ CName c


  ---------------- MT-IntReal     ---------------- MT-FltReal
   ⊢ Int <$ Real                   ⊢ Flt <$ Real

  --------------- MT-IntNum     --------------- MT-FltNum     ----------------- MT-CmplxNum
   ⊢ Int <$ Num                  ⊢ Flt <$ Num                  ⊢ Cmplx <$ Num


  --------------------- MT-ExtExt     ------------------ MT-ExtAName
   ⊢ Ext<an> <$ Ext<an>                ⊢ Ext<an> <$ an

  --------------------- MT-ExtRealNum 
   ⊢ Ext<Real> <$ Num                


   ⊢ τ1 <$ τ1'  ⊢ τ2 <$ τ2'
  -------------------------- MT-Pair
      ⊢ τ1×τ2 <$ τ1'×τ2'


     ⊢ τ1 <$ τ1'                      ⊢ τ2 <$ τ2'
  ----------------- MT-Union1     ------------------ MT-Union2
   ⊢ τ1 <$ τ1'∪τ2'                  ⊢ τ2 <$ τ1'∪τ2'

*)

Reserved Notation "'|-' t1 '<$' t2" (at level 50).

(** Matching of value types *)
Inductive match_ty : ty -> ty -> Prop :=                                 
(* CName *)
| MT_CName : forall (c : cname),
    |- TCName c <$ TCName c

(* Real *)
| MT_IntReal : |- tint <$ treal
| MT_FltReal : |- tflt <$ treal
(* Num *)
| MT_IntNum   : |- tint <$ tnum
| MT_FltNum   : |- tflt <$ tnum
| MT_CmplxNum : |- tcmplx <$ tnum
(* Ext *)
| MT_ExtExt   : forall (a : aname),
    |- TExt a <$ TExt a
| MT_ExtAName : forall (a : aname),
    |- TExt a <$ TAName a
| MT_ExtRealNum  : |- TExt NReal <$ tnum                          
                          
(* Pair *)
| MT_Pair : forall t1 t2 t1' t2',
    |- t1 <$ t1' ->
    |- t2 <$ t2' ->
    |- TPair t1 t2 <$ TPair t1' t2'
             
(* Union *)
| MT_Union1 : forall t1 t1' t2',
    |- t1 <$ t1' ->
    |- t1 <$ TUnion t1' t2'
| MT_Union2 : forall t2 t1' t2',
    |- t2 <$ t2' ->
    |- t2 <$ TUnion t1' t2'
 
where "|- t1 '<$' t2" := (match_ty t1 t2) : btjm_scope.

Hint Constructors match_ty.

Open Scope btjm_scope.

(** Our _tag-based semantic subtyping_ is defined in terms of
    the matching relation. *)
(** [t1] <= [t2] *)
Definition sem_sub (t1 t2 : ty) :=
  forall (v : ty), value_type v -> |- v <$ t1 -> |- v <$ t2.

Notation "'||-' '[' t1 ']' '<=' '[' t2 ']'" := (sem_sub t1 t2) (at level 50) : btjm_scope.

Hint Unfold sem_sub.

Delimit Scope btjm_scope with btjm.


(* ################################################################# *)
(** ** Normal Form of Types *)
(* ################################################################# *)

(** We are going to use normalized types in the definition of
    reductive subtyping (i.e. syntax-directed algorithmic subtyping)
    as well as in proofs about declarative subtyping.

    Normalized type is a union of atoms, where atoms are
    nominal types or pairs of atoms. Atom types are valid.
    Semantically, an atom type cannot be represented as a finite
    union of valid types, for an abstract nominal type
    "contains" extension types.
 *)

(* ================================================================= *)
(** *** Definition *)
(* ================================================================= *)

Inductive atom_type : ty -> Prop :=
| AT_CName : forall (n : cname),
    atom_type (TCName n)
| AT_AName : forall (n : aname),
    atom_type (TAName n) 
| AT_Pair : forall (ta1 ta2 : ty),
    atom_type ta1 ->
    atom_type ta2 ->
    atom_type (TPair ta1 ta2)
.

Hint Constructors atom_type.
              
Inductive in_nf : ty -> Prop :=
| NF_Atom : forall (ta : ty),
    atom_type ta ->
    in_nf ta
| NF_Union : forall (t1 t2 : ty),
    in_nf t1 ->
    in_nf t2 ->
    in_nf (TUnion t1 t2)
.

Notation "'InNF(' t ')'" := (in_nf t) (at level 30) : btjnf_scope.

Hint Constructors in_nf.

Open Scope btjnf_scope.

(* ----------------------------------------------------------------- *)
(** **** Examples *)
(* ----------------------------------------------------------------- *)

Example innf_1 : InNF(tint).
Proof. repeat constructor. Qed.

Example innf_2 : InNF(TPair tint tstr).
Proof. repeat constructor. Qed.

Example innf_3 : InNF(TUnion (TPair tint tstr) tint).
Proof. apply NF_Union; repeat constructor. Qed.

Example innf_4 : InNF(TPair tint (TUnion tint tstr)) -> False.
Proof. intros Hcontra; inversion Hcontra. inversion H. inversion H4. Qed.

(* ================================================================= *)
(** *** Computing Normal Form *)
(* ================================================================= *)

Fixpoint unite_pairs (t1 : ty) := fix unprs (t2 : ty) :=
  match t1, t2 with
  | TUnion t11 t12, _ => TUnion (unite_pairs t11 t2) (unite_pairs t12 t2)
  | _, TUnion t21 t22 => TUnion (unprs t21)          (unprs t22)
  | _, _              => TPair t1 t2
  end.

Fixpoint mk_nf (t : ty) :=
  match t with
  | TCName n  => t
  | TAName n  => t
  | TPair t1 t2 =>
    let t1' := mk_nf t1 in
    let t2' := mk_nf t2 in
    unite_pairs t1' t2'
  | TUnion t1 t2 =>
    TUnion (mk_nf t1) (mk_nf t2)
  | TExt _    => t   (* we will not use extension types in the surface language *)
  end.

Notation "'MkNF(' t ')'" := (mk_nf t) (at level 30) : btjnf_scope.

(*
Eval compute in (mk_nf tint).
Eval compute in (mk_nf (TPair (TUnion tint tflt) tstr)).
Eval compute in (mk_nf (TPair (TPair (TUnion tint tflt) tstr) tstr)).
*)

Delimit Scope btjnf_scope with btjnf.


(* ################################################################# *)
(** ** Subtyping *)
(* ################################################################# *)

(* ================================================================= *)
(** *** Declarative *)
(* ================================================================= *)

(*
  ---------- SD-Refl
   ⊢ τ << τ

   ⊢ τ1 << τ2   ⊢ τ2 << τ3
  -------------------------- SD-Trans
          ⊢ τ1 << τ3


  --------------- SD-IntReal      ---------------- SD-FltReal
   ⊢ Int << Real                   ⊢ Flt << Real

  ---------------- SD-RealNum     ----------------- SD-CmplxNum
   ⊢ Real << Num                   ⊢ Cmplx << Num


   ⊢ τ1 << τ1'  ⊢ τ2 << τ2'
  -------------------------- SD-Pair
      ⊢ τ1×τ2 << τ1'×τ2'


  --------------- SD-UnionR1     --------------- SD-UnionR2
   ⊢ τ1 << τ1∪τ2                  ⊢ τ2 << τ1∪τ2

   ⊢ τ1 << τ'  ⊢ τ2 << τ'
  ------------------------ SD-UnionL
        ⊢ τ1∪τ2 << τ'  


  ------------------------------------ SD-Distr1
   ⊢ (τ11∪τ12)×τ2 << τ11×τ2 ∪ τ12×τ2 

  ------------------------------------ SD-Distr2
   ⊢ τ1×(τ21∪τ22) << τ1×τ21 ∪ τ1×τ22 
*)

Reserved Notation "'|-' t1 '<<' t2" (at level 50).

Inductive sub_d : ty -> ty -> Prop :=                                 
(* Reflexivity *)
| SD_Refl : forall t,
    |- t << t
(* Transitivity *)
| SD_Trans : forall t1 t2 t3,
    |- t1 << t2 ->
    |- t2 << t3 ->
    |- t1 << t3

(* User-Defined Types *)            
| SD_IntReal :
  |- tint   << treal
| SD_FltReal :
  |- tflt   << treal
| SD_RealNum :
  |- treal  << tnum
| SD_CmplxNum :
  |- tcmplx << tnum
            
(* Pair *)
| SD_Pair : forall t1 t2 t1' t2',
    |- t1 << t1' ->
    |- t2 << t2' ->
    |- TPair t1 t2 << TPair t1' t2'
             
(* Union *)
| SD_UnionL : forall t1 t2 t,
    |- t1 << t ->
    |- t2 << t ->
    |- TUnion t1 t2 << t
| SD_UnionR1 : forall t1 t2,
    |- t1 << TUnion t1 t2
| SD_UnionR2 : forall t1 t2,
    |- t2 << TUnion t1 t2

(* Distributivity *)
| SD_Distr1 : forall t11 t12 t2,
    |- TPair (TUnion t11 t12) t2 << TUnion (TPair t11 t2) (TPair t12 t2)
| SD_Distr2 : forall t1 t21 t22,
    |- TPair t1 (TUnion t21 t22) << TUnion (TPair t1 t21) (TPair t1 t22)
             
where "|- t1 '<<' t2" := (sub_d t1 t2) : btj_scope.

Hint Constructors sub_d.

Open Scope btj_scope.

(* ----------------------------------------------------------------- *)
(** **** Union Right *)
(* ----------------------------------------------------------------- *)

Lemma union_right_1 : forall (t t1 t2 : ty),
    |- t << t1 ->
    |- t << (TUnion t1 t2).
Proof.
  intros t t1 t2 H.
  eapply SD_Trans. eassumption. constructor.
Qed.

Lemma union_right_2 : forall (t t1 t2 : ty),
    |- t << t2 ->
    |- t << (TUnion t1 t2).
Proof.
  intros t t1 t2 H.
  eapply SD_Trans. eassumption. constructor.
Qed.

Hint Resolve union_right_1.
Hint Resolve union_right_2.

(* ----------------------------------------------------------------- *)
(** **** Aux Tactics for Transitivity *)
(* ----------------------------------------------------------------- *)

Ltac solve_trans :=
  eapply SD_Trans; eassumption.

Delimit Scope btj_scope with btj.

(* ================================================================= *)
(** *** Reductive Subtyping (no Transitivity and Distributivity) *)
(* ================================================================= *)

(*
  ----------------------- SR-BaseRefl
   ⊢ CName n << CName n


  --------------- SR-IntReal     --------------- SR-FltReal
   ⊢ Int << Real                  ⊢ Flt << Real

  --------------- SR-RealNum
   ⊢ Real << Num                 

  ----------------- SR-CmplxNum
   ⊢ Cmplx << Num

  -------------- SR-IntNum     --------------- SR-FltNum     
   ⊢ Int << Num                 ⊢ Flt << Num 


   ⊢ τ1 << τ1'  ⊢ τ2 << τ2'
  -------------------------- SR-Pair
      ⊢ τ1×τ2 << τ1'×τ2'


     ⊢ τ1 << τ1'                      ⊢ τ2 << τ2'
  ----------------- SR-UnionR1     ----------------- SR-UnionR2
   ⊢ τ1 << τ1'∪τ2'                  ⊢ τ2 << τ1'∪τ2'

   ⊢ τ1 << τ'  ⊢ τ2 << τ'
  ------------------------ SR-UnionL
        ⊢ τ1∪τ2 << τ'  


   ⊢ NF(τ) << τ'
  --------------- SR-NormalForm
    ⊢ τ << τ'

 *)

Open Scope btjm_scope.

Reserved Notation "'|-' t1 '<<' t2" (at level 50).

Inductive sub_r : ty -> ty -> Prop :=                                 
(* Reflexivity *)
| SR_CNameRefl : forall (c : cname),
    |- TCName c << TCName c
| SR_ANameRefl : forall (a : aname),
    |- TAName a << TAName a

(* User-Defined Types *)            
| SR_IntReal :
  |- tint   << treal
| SR_FltReal :
  |- tflt   << treal
| SR_RealNum :
  |- treal  << tnum
| SR_CmplxNum :
  |- tcmplx << tnum
(* Transitivity *)
| SR_IntNum :
  |- tint   << tnum
| SR_FltNum :
  |- tflt   << tnum
            
(* Pair *)
| SR_Pair : forall t1 t2 t1' t2',
    |- t1 << t1' ->
    |- t2 << t2' ->
    |- TPair t1 t2 << TPair t1' t2'
             
(* Union *)
| SR_UnionL : forall t1 t2 t',
    |- t1 << t' ->
    |- t2 << t' ->
    |- TUnion t1 t2 << t'
| SR_UnionR1 : forall t1 t1' t2',
    |- t1 << t1' ->
    |- t1 << TUnion t1' t2'
| SR_UnionR2 : forall t2 t1' t2',
    |- t2 << t2' ->
    |- t2 << TUnion t1' t2'

(* Distributivity *)
| SR_NormalForm : forall t t',
    |- MkNF(t) << t' ->
    |- t << t'
             
where "|- t1 '<<' t2" := (sub_r t1 t2) : btjr_scope.

Hint Constructors sub_r.

Delimit Scope btjr_scope with btjr.

