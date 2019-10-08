From Coq Require Import
     Setoid Morphisms.
From Games Require Import
     Category CCCops.

Import Carrier.
Import CatNotations.
Local Open Scope cat.

Section TerminalLaws.
  Context {obj : Type} (C : Hom obj).
  Context {Eq2C : Eq2 C} {IdC : Id_ C} {CatC : Cat C}.

  (** There is only one morphism between any object and the terminal object *)
  Class TerminalObject (t : obj) {Terminal_t : Terminal C t} : Prop :=
    terminal_object : forall a (f : C a t), f ⩯ constant.
End TerminalLaws.

Section ProductLaws.

  Context {obj : Type} (C : Hom obj).
  Context {Eq2_C : Eq2 C} {Id_C : Id_ C} {Cat_C : Cat C}.
  Context (bif : binop obj).
  Context {ProdPair_C : ProdPair C bif}
          {ProdPi1_C : ProdPi1 C bif}
          {ProdPi2_C : ProdPi2 C bif}.

  Class PairPi1 : Prop :=
    pair_pi1 : forall a b c (f : C c a) (g : C c b),
      pair f g >>> pi1 ⩯ f.

  Class PairPi2 : Prop :=
    pair_pi2 : forall a b c (f : C c a) (g : C c b),
      pair f g >>> pi2 ⩯ g.

  (** Uniqueness of products *)
  Class PairUniversal : Prop :=
    pair_universal :
      forall a b c (f : C c a) (g : C c b) (fg : C c (bif a b)),
        (fg >>> pi1 ⩯ f) ->
        (fg >>> pi2 ⩯ g) ->
        fg ⩯ pair f g.

  Class Product : Prop := {
                        product_pair_pi1 :> PairPi1;
                        product_pair_pi2 :> PairPi2;
                        product_pair_universal :> PairUniversal;
                        product_proper_pair :> forall a b c,
                            @Proper (C c a -> C c b -> C c _) (eq2 ==> eq2 ==> eq2) pair
                      }.

End ProductLaws.

Arguments pair_pi1 {obj C Eq2_C Cat_C bif ProdPair_C ProdPi1_C PairPi1} [a b c] f g.
Arguments pair_pi2 {obj C Eq2_C Cat_C bif ProdPair_C ProdPi2_C PairPi2} [a b c] f g.
Arguments pair_universal {obj C _ _ bif _ _ _ _} [a b c] f g fg.

Section ExponentialLaws.

  Context {obj : Type} (C : Hom obj).
  Context {Eq2_C : Eq2 C} {Id_C : Id_ C} {Cat_C : Cat C}.
  Context (bif : binop obj)
          {ProdPi1_C : ProdPi1 C bif}
          {ProdPi2_C : ProdPi2 C bif}
          {ProdPair_C : ProdPair C bif}.
  Context (exp : binop obj)
          {Eval_C: Eval C bif exp}
          {Curry_C: Curry C bif exp}
          {Uncurry_C: Uncurry C bif exp}.

  Class EvalCurry : Prop :=
    eval_curry :
      forall a b c (f: C (bif a b) c),
        bimap (curry f) (id_ b) >>> eval ⩯ f.

  Class CurryUnique : Prop :=
    curry_unique :
      forall a b c (f: C (bif a b) c)
        (g: C a (exp c b)),
        bimap g (id_ b) >>> eval ⩯ f ->
        curry f ⩯ g.

  Class EvalUncurry : Prop :=
    eval_uncurry :
      forall a b c (g: C a (exp c b)),
        bimap g (id_ b) >>> eval ⩯ uncurry g.

  Class UncurryUnique : Prop :=
    uncurry_unique :
      forall a b c (f: C (bif a b) c)
        (g: C a (exp c b)),
        bimap g (id_ b) >>> eval ⩯ f ->
        uncurry g ⩯ f.

End ExponentialLaws.

Section CurryUncurry.

  Context {obj : Type} (C : Hom obj) (bif : binop obj).
  Context {Eq2_C : Eq2 C} {Cat_C: Cat C} {Id_C: Id_ C} {Category_C: Category C}.
  Context {ProdPair_C : ProdPair C bif}
          {ProdPi1_C : ProdPi1 C bif}
          {ProdPi2_C : ProdPi2 C bif}.
  Context (exp: binop obj)
          {Eval_C: Eval C bif exp}
          {Curry_C: Curry C bif exp}
          {Uncurry_C: Uncurry C bif exp}
          {EvalCurry_C: EvalCurry C bif exp}
          {CurryUnique_C: CurryUnique C bif exp}
          {EvalUncurry_C: EvalUncurry C bif exp}
          {UncurryUnique_C: UncurryUnique C bif exp}.

  Lemma UncurryCurry:
      forall a b c (f: C (bif a b) c),
        uncurry (curry f) ⩯ f.
  Proof.
    intros a b c f.
    eapply uncurry_unique; eauto.
  Qed.

  Lemma CurryUncurry:
      forall a b c (g: C a (exp c b)),
        curry (uncurry g) ⩯ g.
  Proof.
    intros a b c f.
    eapply curry_unique; eauto.
  Qed.

End CurryUncurry.

Section UncurryasEval.

  Context {obj : Type} (C : Hom obj) (bif : binop obj).
  Context {Cat_C: Cat C} {Id_C: Id_ C} {Eq2_C: Eq2 C}.
  Context {ProdPair_C : ProdPair C bif}
          {ProdPi1_C : ProdPi1 C bif}
          {ProdPi2_C : ProdPi2 C bif}.
  Context (exp: binop obj)
          {Eval_C: Eval C bif exp} .
  Context {Eq2_Refl: forall A B, Reflexive (@eq2 _ _ _ A B)}.

  Global Instance Uncurry_Eval : Uncurry C bif exp :=
    fun a b c f => bimap f (id_ b) >>> eval.

  Global Instance EvalUncurry_Eval: EvalUncurry C bif exp.
  Proof.
    intros a b c g.
    reflexivity.
  Qed.

  Global Instance UncurryUnique_Eval: UncurryUnique C bif exp.
  Proof.
    intros a b c f g EQ; apply EQ.
  Qed.

End UncurryasEval.

