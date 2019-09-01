From Games Require Import
     Utils.

From Coq Require Import
     Relations.

Section Arena.

  Class Arena :=
    {
      M:> Type;
      Q: M -> Prop;
      O: M -> Prop;
      I: M -> Prop;
      enable: M -> M -> Prop
    }.

  Definition A `{Arena} := fun m => ~ Q m.
  Definition P `{Arena} := fun m => ~ O m.

  Infix "⊢" := enable (at level 50).

  Record Arena_WF `{Arena} :=
    {
      init_WF: forall m, I m -> Q m /\ O m;
      e1: forall m n, m ⊢ n -> Q m;
      e2: forall m n, m ⊢ n -> (O m <-> P n);
      e3: forall m n, m ⊢ n -> ~ I n
    }.

End Arena.

Infix "⊢" := enable (at level 50).
Notation "⟨ M , Q , O , I , R ⟩" := (Build_Arena M Q O I R). 

Section Relations.

  Section Pred.
    
    Definition TT {A: Type}: A -> Prop := fun _ => True.
    Definition FF {A: Type}: A -> Prop := fun _ => False.

    Inductive Sum_Pred {A B: Type} (P1: A -> Prop) (P2: B -> Prop): (A + B) -> Prop :=
    | Sum_Pred_L: forall a, P1 a -> Sum_Pred P1 P2 (inl a) 
    | Sum_Pred_R: forall b, P2 b -> Sum_Pred P1 P2 (inr b).

    Inductive Inl_Pred {A B: Type} (P1: A -> Prop): (A + B) -> Prop :=
    | Inl_PredC: forall a, P1 a -> Inl_Pred P1 (inl a).

    Inductive Inr_Pred {A B: Type} (P2: B -> Prop): (A + B) -> Prop :=
    | Inr_PredC: forall b, P2 b -> Inr_Pred P2 (inr b).
  End Pred.

  Section Rel.

    Definition TT' {A: Type}: relation A := fun _ _ => True.
    Definition FF' {A: Type}: relation A := fun _ _ => False.

    Inductive Prod_Pred_to_Rel {A B: Type} (P1: A -> Prop) (P2: B -> Prop): A -> B -> Prop :=
    | Prod_PredC: forall a b, P1 a -> P2 b -> Prod_Pred_to_Rel P1 P2 a b.

    Inductive Sum_Rel {A B: Type} (R1: relation A) (R2: relation B): relation (A + B) :=
    | Sum_Rel_L: forall a a', R1 a a' -> Sum_Rel R1 R2 (inl a) (inl a')
    | Sum_Rel_R: forall b b', R2 b b' -> Sum_Rel R1 R2 (inr b) (inr b').

    Inductive Join_Rel {A: Type} (R1 R2: relation A): relation A :=
    | Join_Rel_L: forall a a', R1 a a' -> Join_Rel R1 R2 a a'
    | Join_Rel_R: forall b b', R2 b b' -> Join_Rel R1 R2 b b'.

  End Rel.

End Relations.

Infix "+'" := Sum_Pred (at level 40).
Notation "'inl_' P" := (Inl_Pred P) (at level 5).
Notation "'inr_' P" := (Inr_Pred P) (at level 5).
Infix "->'" := (Prod_Pred_to_Rel) (at level 40).
Infix "+''" := Sum_Rel (at level 40).
Infix "∪" := Join_Rel (at level 60).

Inductive void: Type :=.

Section Arena_Constructs.

  Section Product.

    Definition Prod_Arena (A1 A2: Arena): Arena :=
      ⟨
        @M A1 + @M A2,
        Q +' Q,
        O +' O,
        I +' I,
        enable +'' enable
      ⟩.

    Definition Unit_Arena: Arena :=
      ⟨
        void,
        FF,
        FF,
        FF,
        FF'
      ⟩.

  End Product.

  Section Arrow.

    Definition Arrow_Arena (A1 A2: Arena): Arena :=
      {|
        M := @M A1 + @M A2;
        Q := Q +' Q;
        O := P +' O;
        I := inr_ (@I A2);
        enable := (@enable A1 +'' @enable A2) ∪ (inr_ I ->' inl_ I)
      |}.

  End Arrow.

End Arena_Constructs.

Notation "'1'" := Unit_Arena.
Infix "⊗" := Prod_Arena (at level 29, left associativity).
Infix "↪" := Arrow_Arena (at level 11, left associativity).

(* TODO: Define the isomorphism of Arenas up to which we work. Prove that 1 is indeed a unit for the product, 
 *)

Section Arena_Examples.

  Inductive Nat_enable: unit + nat -> unit + nat -> Prop :=
  | Nat_E: forall n, Nat_enable (inl tt) (inr n).

  Definition Nat_Arena: Arena :=
    ⟨ unit + nat,
      inl_ TT,
      inl_ TT,
      inl_ TT,
      Nat_enable
    ⟩.



End Arena_Examples.