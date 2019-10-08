From Coq Require Import
     Setoid Morphisms.
From Games Require Import
     Category.

Import Carrier.
Import CatNotations.
Local Open Scope cat.

Section CartesianOps.

  Context {obj : Type} (C : Hom obj) (bif : binop obj).

  (** If there is a terminal object [t], its terminal morphisms are written
    [constant : C a t]. *)
  Class Terminal (t : obj) := constant : forall a, C a t.

  Class ProdPair :=
    pair: forall a b c,
      C c a -> C c b -> C c (bif a b).

  Class ProdPi1 :=
    pi1: forall a b, C (bif a b) a.

  Class ProdPi2 :=
    pi2: forall a b, C (bif a b) b.

End CartesianOps.
Arguments constant {obj C t Terminal a}.
Arguments pair {obj C bif ProdPair a b c}.
Arguments pi1 {obj C bif ProdPi1 a b}.
Arguments pi2 {obj C bif ProdPi2 a b}.

Section CartesianConstruct.

Context {obj : Type} (C : Hom obj) (Cat_C : Cat C).
Variables (PAIR : binop obj) (Prod_PAIR : ProdPair C PAIR)
          (ProdPi1_PAIR : ProdPi1 C PAIR)
          (ProdPi2_PAIR : ProdPi2 C PAIR).

(** Coproducts are bifunctors. *)
Global Instance Bimap_Product : Bimap C PAIR :=
  fun a b c d (f : C a c) (g : C b d) =>
    pair (pi1 >>> f) (pi2 >>> g).

(** Products are symmetric. *)

Global Instance Swap_Product : Swap C PAIR :=
  fun a b => pair pi2 pi1.

(** Coproducts are associative. *)

Global Instance AssocR_Coproduct : AssocR C PAIR :=
  fun a b c => pair (pi1 >>> pi1) (pair (pi1 >>> pi2) pi2).

Global Instance AssocL_Coproduct : AssocL C PAIR :=
  fun a b c => pair (pair pi1 (pi2 >>> pi1)) (pi2 >>> pi2).

Variables (Id_C : Id_ C) (T : obj) (Terminal_T: Terminal C T).

(** The terminal object is a unit for the product. *)

Global Instance UnitL_Product : UnitL C PAIR T :=
  fun a => pi2.

Global Instance UnitL'_Product : UnitL' C PAIR T :=
  fun a => pair constant (id_ a).

Global Instance UnitR_Product : UnitR C PAIR T :=
  fun a => pi1.

Global Instance UnitR'_Product : UnitR' C PAIR T :=
  fun a => pair (id_ a) constant.

End CartesianConstruct.

Section ExponentialOps.

  Context {obj : Type} (C : Hom obj) (bif : binop obj).
  Context {ProdPair_C : ProdPair C bif}
          {ProdPi1_C : ProdPi1 C bif}
          {ProdPi2_C : ProdPi2 C bif}.
  Context (exp: binop obj).

  Class Eval :=
    eval: forall a b, C (bif (exp a b) b) a.

  Class Curry :=
    curry: forall a b c,
      C (bif a b) c -> C a (exp c b).

  Class Uncurry :=
    uncurry: forall a b c,
      C a (exp c b) -> C (bif a b) c.

End ExponentialOps.
Arguments eval {obj C bif exp Eval a b}.
Arguments curry {obj C bif exp Curry a b c}.
Arguments uncurry {obj C bif exp Uncurry a b c}.

