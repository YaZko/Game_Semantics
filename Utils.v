From Coq Require Import
     List
     Relations.
Import ListNotations.

(** General purpose tactics **)
Ltac inv H := inversion H; subst; clear H.

Ltac flatten_goal :=
  match goal with
  | |- context[match ?x with | _ => _ end] => let Heq := fresh "Heq" in destruct x eqn:Heq
  end.

Ltac flatten_hyp h :=
  match type of h with
  | context[match ?x with | _ => _ end] => let Heq := fresh "Heq" in destruct x eqn:Heq
  end.

Ltac flatten_all :=
  match goal with
  | h: context[match ?x with | _ => _ end] |- _ => let Heq := fresh "Heq" in destruct x eqn:Heq
  | |- context[match ?x with | _ => _ end] => let Heq := fresh "Heq" in destruct x eqn:Heq
  end.

(****************************** Lists ******************************)

Inductive prefix {A: Type}: relation (list A) :=
| Nil_Prefix: forall l, prefix [] l
| Cons_Prefix: forall l x l', prefix l l' -> prefix (x :: l) (x :: l').
Hint Constructors prefix.
Infix "⊑" := prefix (at level 40).

Infix "∈" := In (at level 40).

Definition snoc {A: Type} (l: list A) a: list A := l ++ [a].

Inductive snoc_view {A: Type}: list A -> Type :=
| Nil: snoc_view nil
| Snoc: forall xs x, snoc_view (snoc xs x).

Fixpoint view {X: Type} (xs: list X): snoc_view xs :=
  match xs with
  | [] => Nil
  | x :: xs =>
    match view xs with
    | Nil => Snoc [] x
    | Snoc ys y => Snoc (x::ys) y
    end
  end.

Lemma snoc_not_nil_l: forall {A: Type} (xs: list A) x, [] = snoc xs x -> False.
Proof.
  intros ? xs ? abs; destruct xs; inv abs.
Qed.

Lemma snoc_not_nil_r: forall {A: Type} (xs: list A) x, snoc xs x = [] -> False.
Proof.
  intros ? xs ? abs; destruct xs; inv abs.
Qed.
Hint Resolve snoc_not_nil_l snoc_not_nil_r.

Lemma snoc_inj : forall {A: Type} (xs ys: list A) x y
                   (EQ: snoc xs x = snoc ys y),
    xs = ys /\ x = y.
Proof.
  induction xs as [| x' xs IH]; cbn; intros.
  - destruct ys as [| ys y']; [inv EQ; auto |].
    inv EQ.
    exfalso; eauto.
  - destruct ys as [| ys y']; eauto; cbn in *.
    + destruct xs; inv EQ; exfalso; eauto. 
    + inv EQ; edestruct IH; eauto; subst; auto.
Qed.

Ltac snoc_inv H :=
  apply snoc_inj in H; destruct H; subst; clear H.

Lemma snoc_inv: forall {X: Type} (xs: list X),
    xs = [] \/ exists xs' x, xs = snoc xs' x.
Proof.
  induction xs as [| x xs IH] using rev_ind; cbn; eauto.
  right; destruct IH as [-> | (? & ? & ->)].
  exists []; eexists; reflexivity. 
  do 2 eexists; reflexivity. 
Qed.

Ltac destruct_snoc xs :=
  generalize (snoc_inv xs); intros [-> | (? & ? & ->)]. 

Lemma prefix_snoc: forall {X: Type} (xs xs': list X) x,
    xs' ⊑ snoc xs x ->
    xs' = snoc xs x \/ xs' ⊑ xs.
Proof.
  induction xs as [| xs x' IH]; cbn; intros xs' x PRE.
  - inv PRE; eauto.
    inv H1; eauto.
  - destruct xs'; auto.
    inv PRE.
    edestruct IH; eauto.
    subst; eauto.
Qed.

Notation "x [[ n ]]" := (nth_error x n) (at level 12).

(**************************** Utilites for predicates and relations **************************)

Section Relations.

  (**
     Utilities to manipulates predicates and relations.
     Should eventually be moved somewhere else.
   *)
  Section Pred.

    Definition pred (A: Type) := A -> Prop.

    Definition TT {A: Type}: pred A := fun _ => True.
    Definition FF {A: Type}: pred A := fun _ => False.

    Inductive Sum_Pred {A B: Type} (P1: pred A) (P2: pred B): pred (A + B) :=
    | Sum_Pred_L: forall a, P1 a -> Sum_Pred P1 P2 (inl a) 
    | Sum_Pred_R: forall b, P2 b -> Sum_Pred P1 P2 (inr b).

    Inductive Inl_Pred {A B: Type} (P1: pred A): pred (A + B) :=
    | Inl_PredC: forall a, P1 a -> Inl_Pred P1 (inl a).

    Inductive Inr_Pred {A B: Type} (P2: pred B): pred (A + B) :=
    | Inr_PredC: forall b, P2 b -> Inr_Pred P2 (inr b).

    Definition Sub_Pred {A: Type} (P Q: pred A): Prop :=
      forall a, P a -> Q a.

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
Infix "⊆" := Sub_Pred (at level 60).
Infix "⊆'" := inclusion (at level 60).
