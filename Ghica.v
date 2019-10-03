From Games Require Import
     Utils.

From Coq Require Import
     List
     Relations
     Nat.
Import ListNotations.
Require Import Omega.
(**
   We now implement "The far side of the cube" as described by Dan R. Ghica.
   It is stated as being the simplest traditional game semantics in the sense
   that very few restrictions are put on the structure. In this sense, it is
   not a very interesting domain since it is too large for definability to hold
   when taken as a model of a programming language.
   However it is a good starting point upon which enforce additional constraints
   to model various programming constructs.
   This approach is referred to as "Abramsky's Cube".
 *)

Section Arena.

  (**
     [Arena]s are the basic structure upon which games are played.
     It contains:
     - a type [M] of moves that can be taken;
     - a subset of moves [Q] that are interpreted as queries;
     - a subset of moves [O] that are assigned to the opponent;
     - a subset of moves [I] that are initial;
     - a relation of moves stating how taking a move enables new moves to become legal.
   *)

  Class Arena :=
    {
      M:> Type;
      Q: M -> Prop;
      O: M -> Prop;
      I: M -> Prop;
      enable: M -> M -> Prop
    }.

  (* The complement of [Q] are answers [A] *)
  Definition A `{Arena} := fun m => ~ Q m.
  (* The complement of [O] are player moves [P] *)
  Definition P `{Arena} := fun m => ~ O m.

  Infix "⊢" := enable (at level 50).

  (**
     Constraints are then enforced on arenas:
     - Initial moves are exclusively queries by opponent;
     - Only queries can enable new moves;
     - Plays are alternating: a move of a polarity can only enable moves of the other polarity;
     - Initial move cannot be enabled.
   *)
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

Inductive void: Type :=.

Section Arena_Constructs.

  (**
     We can then construct combinators over arenas.
   *)

    (* The product is a straightforward join of both arenas.
       Intuitively, both games are played in parallel without any interaction.
     *)
    Definition Prod_Arena (A1 A2: Arena): Arena :=
      ⟨
        @M A1 + @M A2,
        Q +' Q,
       O +' O,
        I +' I,
        enable +'' enable
      ⟩.

    (* The unit arena contains no move. *)
    Definition Unit_Arena: Arena :=
      ⟨
        void,
        FF,
        FF,
        FF,
        FF'
      ⟩.

    (* The arrow arena contains the union of moves.
       However, the polarity of the game to the left of the arrow is reversed.
       The game starts to the right of the arrow.
       Finally, inital moves to the right of the arrow enables the ones to the left.
     *)
    Definition Arrow_Arena (A1 A2: Arena): Arena :=
      {|
        M := @M A1 + @M A2;
        Q := Q +' Q;
        O := P +' O;
        I := inr_ (@I A2);
        enable := (@enable A1 +'' @enable A2) ∪ (inr_ I ->' inl_ I)
      |}.


    Definition Sub_Arena (A : Arena) (P : M -> Prop) :=
      {|
        M := {m : M | P m};
        Q := fun m => match m with exist _ m' _  => Q m' end;
        O := fun m => match m with exist _ m' _ => O m' end;
        I := fun m => match m with exist _ m' _ => I m' end;
        enable := fun m n => match m with exist _ m' _  => match n with exist _ n' _  => enable m' n' end end;

      |}.

End Arena_Constructs.

Notation "'Unit'" := Unit_Arena.
Infix "⊗" := Prod_Arena (at level 29, left associativity).
Infix "↪" := Arrow_Arena (at level 11, right associativity).

(* TODO: Define the isomorphism of Arenas up to which we work.
   Prove that 1 is indeed a unit for the product and arrow.
 *)

Definition bijection {A B : Type} (f : A -> B) :=
  (forall x y, f x = f y -> x = y) /\ (forall y, exists x, f x = y).

Definition arena_isomorphism {A1 A2 : Arena} (f : @M A1 -> @M A2) : Prop :=
  bijection f /\ forall m n, (@Q A1 m <-> @Q A2 (f m)) /\ (@O A1 m <-> @O A2 (f m)) /\
                 (@I A1 m <-> @I A2 (f m)) /\ (@enable A1 m n <-> @enable A2 (f m) (f n)).

Definition isomorphic (A1 A2 : Arena) : Prop := exists f, @arena_isomorphism A1 A2 f.

Lemma iso_reflexive : forall A, isomorphic A A.
Proof.
  intros. unfold isomorphic, arena_isomorphism. exists (fun x => x).
  split.
  - unfold bijection. intros. split; auto.
    intros. exists y. auto.
  - intros. repeat split; auto.
Qed.

Lemma iso_symmetric : forall A1 A2, isomorphic A1 A2 -> isomorphic A2 A1.
Proof.
  intros. unfold isomorphic, arena_isomorphism in *. destruct H as [f [Hbi Hiso] ].
(** is yielding an inverse function from a bijection constructive?  *)
Admitted.




Lemma iso_transitive : forall A1 A2 A3, isomorphic A1 A2 -> isomorphic A2 A3 -> isomorphic A1 A3.
  intros. unfold isomorphic, arena_isomorphism.
  destruct H as [f12 [Hbi12 Hiso12] ]. destruct H0 as [f23 [Hbi23 Hiso23] ].
  exists (fun x => f23 (f12 x) ). split; intros; repeat split;
  try (intros; specialize (Hiso12 m n); specialize (Hiso23 (f12 m) (f12 n)); tauto).
  - intros. unfold bijection in *. destruct Hbi12. apply H0. destruct Hbi23. apply H2. auto.
  - intros. unfold bijection in *. destruct Hbi23 as [ _ Hbi23]. destruct Hbi12 as [ _ Hbi12].
    specialize (Hbi23 y). destruct Hbi23 as [x' Hx']. specialize (Hbi12 x'). destruct Hbi12 as [ x'' Hx''].
    exists x''. subst. auto.
Qed.


Definition isol {A : Arena} (m : void + M) : M :=
  match m with
  | inl v => match v return M with end
  | inr m' => m' end.

Lemma isol_bij : forall A, bijection (@isol A).
Proof.
  intros. unfold bijection. split; intros.
  - destruct x; destruct y; try contradiction; simpl in *.
    subst. auto.
  - exists (inr y). auto.
Qed.



Definition isor {A : Arena} (m : M + void) : M :=
  match m with
  | inl m' => m'
  | inr v => match v return M with end
  end.

Lemma isor_bij : forall A, bijection (@isor A).
Proof.
  intros. unfold bijection. split; intros.
  - destruct x; destruct y; try contradiction; simpl in *. subst. auto.
  - exists (inl y). auto.
Qed.

Lemma unit_left_id_product : forall (A : Arena), exists (f : void + M -> M),
      @arena_isomorphism (Prod_Arena Unit A) A f.
  Proof.
    intro A. exists isol. unfold arena_isomorphism, bijection. split.
    - apply isol_bij.
    - intros. repeat split; intros;
      try (destruct m; try contradiction; simpl in *; inv H; try contradiction; auto);
      try (destruct m; try contradiction; simpl in *; constructor; assumption).
      destruct m; destruct n; try contradiction. simpl in *. constructor. assumption.
  Qed.

Lemma unit_right_id_product : forall (A : Arena), exists (f : M + void -> M),
        @arena_isomorphism (Prod_Arena A Unit) A f.
  Proof.
    intros A. exists isor. unfold arena_isomorphism, bijection. split.
    - apply isor_bij.
    - intros. repeat split; intros;
      try (destruct m; try contradiction; simpl in *; inv H; try contradiction; auto);
      try (destruct m; try contradiction; simpl in *; constructor; assumption).
      destruct m; destruct n; try contradiction. simpl in *. constructor. assumption.
  Qed.

Lemma unit_left_id_exp : forall (A : Arena), exists (f : void + M -> M),
        @arena_isomorphism (Arrow_Arena Unit A) A f.
  Proof.
    intros A. exists isol. unfold arena_isomorphism, bijection. split.
    - apply isol_bij.
    - intros. repeat split; intros;
      try (destruct m; try contradiction; simpl in *; inv H; try contradiction; auto);
      try (destruct m; try contradiction; simpl in *; constructor; assumption).
      + inv H0. simpl. assumption.
      + inv H0. inv H1. contradiction.
      + destruct m; destruct n; try contradiction. simpl in *. repeat constructor. auto.
  Qed.

Definition iso_curry {A B C : Arena} (m : @M A + (@M B + @M C)) : (@M A + @M B) + @M C :=
  match m with
  | inl a => inl (inl a)
  | inr bc =>
    match  bc with
    | inl b => inl (inr b)
    | inr c => inr c
    end
  end.
Set Printing Implicit.
Lemma iso_curry_bij : forall A B C, bijection (@iso_curry A B C).
Proof.
  intros. unfold bijection. split; intros.
  - repeat match goal with | [x : ?T1 + ?T2 |- _] => destruct x end;  simpl in *;
      try discriminate;
      try injection H; intros; simpl in *; subst; auto.
  - repeat match goal with
           | [x : ?T1 + ?T2 |- _ ] => destruct x
           end.
    + exists (inl m). auto.
    + exists (inr (inl m)). auto.
    + exists (inr (inr m)). auto.
Qed.




Lemma wf_init_prod : forall (A B : Arena), @Arena_WF A -> @Arena_WF B -> forall m,
                                               @I (Prod_Arena A B) m -> @Q (Prod_Arena A B) m /\ @O (Prod_Arena A B) m.
Proof.
  intros A B. intros. simpl in *.
  destruct H as [ Ha _ _ _  ]. destruct H0 as [ Hb _ _ _  ]. inv H1.
  - apply Ha in H. destruct H. split; constructor; auto.
  - apply Hb in H. destruct H. split; constructor; auto.
Qed.

Lemma wf_e1_prod : forall (A B : Arena), @Arena_WF A -> @Arena_WF B -> forall (m n : @M (Prod_Arena A B)),
                                             enable m n -> Q m.
Proof.
  intros A B. intros. simpl in *. destruct H as [ _ Ha _ _ ]. destruct H0 as [ _ Hb _ _  ].
  inv H1.
  - apply Ha in H. constructor. auto.
  - apply Hb in H. constructor. auto.
Qed.

Lemma wf_e2_prod : forall (A B : Arena), @Arena_WF A -> @Arena_WF B -> forall (m n : @M (Prod_Arena A B)),
                                             enable m n -> O m <-> P n.
Proof.
  intros A B. intros. simpl in *. destruct H as [ _ _ Ha _  ]. destruct H0 as [ _ _ Hb _  ].
  inv H1.
  - apply Ha in H. split.
    + intros. inv H0. apply H in H2. intro. inv H0.
      contradiction.
    + intros. constructor. unfold P in H0. apply H. intro. apply H0. constructor; auto.
  - apply Hb in H. split.
    + intros. inv H0. apply H in H2. intro. inv H0.
      contradiction.
    + intros. constructor. unfold P in H0. apply H. intro. apply H0. constructor; auto.
Qed.

Lemma wf_e3_prod : forall (A B : Arena), @Arena_WF A -> @Arena_WF B -> forall (m n : @M (Prod_Arena A B)),
                                             enable m n -> ~ I n.
Proof.
  intros A B. intros. simpl in *. destruct H as [ _ _ _ Ha  ]. destruct H0 as [ _ _ _ Hb ].
  intro. inv H1; inv H.
  - apply Ha in H0. auto.
  - apply Hb in H0. auto.
Qed.


Lemma wf_prod : forall (A B : Arena), @Arena_WF A -> @Arena_WF B -> @Arena_WF (Prod_Arena A B).
Proof.
  intros A B Ha Hb. constructor.
  - apply wf_init_prod; auto.
  - apply wf_e1_prod; auto.
  - apply wf_e2_prod; auto.
  - apply wf_e3_prod; auto.
Qed.


Lemma wf_init_arrow : forall (A B : Arena), @Arena_WF A -> @Arena_WF B -> forall (m : @M (Arrow_Arena A B)),
                                                I m -> Q m /\ O m.
Proof.
  intros A B Ha Hb m Hm. destruct Ha as [ Ha _ _ _ ]. destruct Hb as [ Hb _ _ _ ].
  simpl in *. inv Hm. apply Hb in H. split; constructor; tauto.
Qed.

Lemma wf_e1_arrow : forall (A B : Arena), @Arena_WF A -> @Arena_WF B -> forall (m n : @M (Arrow_Arena A B)),
                                              enable m n -> Q m.
Proof.
  intros A B Ha Hb m n Hmn. destruct Ha as [ _ Ha _ _ ]. destruct Hb as [ Hbq Hb _ _  ]. simpl in *.
  inv Hmn.
  - inv H.
    + apply Ha in H0. constructor. auto.
    + apply Hb in H0. constructor. auto.
  - inv H. inv H0. inv H1. constructor. apply Hbq in H. tauto.
Qed.

Lemma wf_e2_arrow : forall (A B : Arena), @Arena_WF A -> @Arena_WF B -> forall (m n : @M (Arrow_Arena A B)),
                                             enable m n -> O m <-> P n.
Proof.
  intros A B Ha Hb m n Hmn. split; intros; simpl in *.
  - intro. simpl in *. inv H; inv H0.
    + destruct Ha. destruct Hb. apply H1. apply e5 with (n := a0); auto.
      inv Hmn.
      * inv H0. auto.
      * inv H0. inv H2.
    + destruct Ha. destruct Hb. apply H1. inv Hmn.
      * inv H0.
      * inv H0. inv H2.
    + inv Hmn; inv H0. inv H2. inv H3. destruct Ha. apply init_WF0 in H2. unfold P in H. tauto.
    + inv Hmn; inv H0.
      * destruct Hb. apply e5 in H4. unfold P in H4. tauto.
      * inv H3.
  - inv Hmn; inv H0; simpl in *.
    + constructor. intro. apply H. simpl. constructor. intro. destruct Ha. apply e5 in H1. unfold P in H1. tauto.
    + constructor. unfold P in H. simpl in *. destruct Hb. apply e5 in H1. apply H1. intro. apply H. constructor.
      auto.
    + inv H1. inv H2. constructor. destruct Hb. apply init_WF0 in H0. tauto.
Qed.

Lemma wf_e3_arrow : forall (A B : Arena), @Arena_WF A -> @Arena_WF B -> forall (m n : @M (Arrow_Arena A B)),
                                              enable m n -> ~ I n.
Proof.
  intros A B Ha Hb m n Hmn. simpl in *. intro. inv H. inv Hmn.
  - inv H. destruct Hb. apply e6 in H3. tauto.
  - inv H. inv H1. inv H2.
Qed.


Lemma wf_arrow : forall (A B : Arena), @Arena_WF A -> @Arena_WF B -> @Arena_WF (Arrow_Arena A B).
Proof.
  intros A B Ha Hb. constructor.
  - apply wf_init_arrow; auto.
  - apply wf_e1_arrow; auto.
  - apply wf_e2_arrow; auto.
  - apply wf_e3_arrow; auto.
Qed.

Lemma enable_comp : forall (A B C : Arena) (a : @M A) (b : @M B) (c : @M C),
    @enable (Arrow_Arena A B)  (inr b) (inl a) ->
    @enable (Arrow_Arena B C) (inr c) (inl b) ->
    @enable (Arrow_Arena A C) (inr c) (inl a).
Proof.
  intros A B C a b c Hba Hbc.
  (** show that a b and c are all initial *)
  inv Hba; inv H. inv H0. inv H1. right. repeat constructor; auto.
  inv Hbc; inv H. inv H1. inv H3. auto.
Qed.


(** could probably parts of automate this  *)


Inductive even : nat -> Prop :=
  | ev_0 : even 0
  | ev_SS (n : nat) (H : even n) : even (S (S n)).


Lemma currying : forall (A B C : Arena),
    exists (f : @M A + (@M B + @M C) -> (@M A + @M B) + @M C),
                 @arena_isomorphism  (Arrow_Arena A (Arrow_Arena B C)) (Arrow_Arena (Prod_Arena A B) C) f.
  Proof.
    intros A B C.
    intros.
    exists iso_curry. unfold arena_isomorphism, bijection. split.
    - apply iso_curry_bij.
   - intros. repeat split; intros; simpl in *;
               repeat match goal with
                  | [H  : (?P ?A +' _) _ |- _] => inv H
                  | [m : ?T1 + ?T2 |- _] => destruct m
                  | [ H : inl ?m = inr ?n  |- _] => discriminate
                  | [ H : inr ?m = inl ?n |- _] => discriminate
                  | [ H : inl ?m = inl ?n |- _ ] => injection H; clear H; intros
                  | [ H : inr ?m = inr ?n |- _ ] => injection H; clear H; intros
                  | [ |- (_ +' _) (inl ?m)  ] => constructor
                  | [ |- (_ +' _) (inr ?m) ] => constructor
                  | [ H : ?P |- P] => assumption
                  | [ |- @P _ _] => intro
                  | [ H : @P _ _ |- False ] => apply H
                  | [ H : inr_ _ _ |- _] => inv H
                  | [ H : inl_ _ _ |- _ ] => inv H
                  | [ |- inr_ _ _ ] => constructor
                  | [ |- inl_ _ _ ] => constructor
                  | [H : @Join_Rel _ _ _ _ _ |- _ ] => inv H
                  | [H : (_ +'' _) _ _ |- _  ] => inv H
                  | [ H : (_ ->' _) _ _ |- _ ] => inv H
                  | _ => simpl in *; subst
                  end; auto.
     all : repeat match goal with
           | [H : enable ?m ?n  |- _ ] => repeat constructor; auto
           end.
     + right. repeat constructor; auto.
     + right. repeat constructor; auto.
     + right. repeat constructor; auto.
     + left. right. right. repeat constructor; auto.
Qed.

  (* YZ: Here is an alternative way to automate. The advantage of this is that it might be reused more easily in other proofs *)

  (* These lemmas should be moved to Utils, they help automating reasoning about [P] since its defined as the negation of [O] *)
  Lemma Sum_Pred_negL: forall {A B: Type} (P: Utils.pred A) (Q: Utils.pred B) x, ~ P x <-> ~ (P +' Q) (inl x).
  Proof.
    split.
    intros ? abs; inv abs; auto.
    intros H ?; apply H; constructor; auto.
  Qed.

  Lemma Sum_Pred_negL_backward: forall {A B: Type} (P: Utils.pred A) (Q: Utils.pred B) x, ~ P x -> ~ (P +' Q) (inl x).
  Proof.
    intros; apply Sum_Pred_negL; auto.
  Qed.

  Lemma Sum_Pred_negL_forward: forall {A B: Type} (P: Utils.pred A) (Q: Utils.pred B) x, ~ (P +' Q) (inl x) -> ~ P x.
  Proof.
    intros ? ? ? ? ?; rewrite <- Sum_Pred_negL; auto.
  Qed.

  Lemma Sum_Pred_negR: forall {A B: Type} (P: Utils.pred A) (Q: Utils.pred B) x, ~ Q x <-> ~ (P +' Q) (inr x).
  Proof.
    split.
    intros ? abs; inv abs; auto.
    intros H ?; apply H; constructor; auto.
  Qed.

  Lemma Sum_Pred_negR_backward: forall {A B: Type} (P: Utils.pred A) (Q: Utils.pred B) x, ~ Q x -> ~ (P +' Q) (inr x).
  Proof.
    intros; apply Sum_Pred_negR; auto.
  Qed.

  Lemma Sum_Pred_negR_forward: forall {A B: Type} (P: Utils.pred A) (Q: Utils.pred B) x, ~ (P +' Q) (inr x) -> ~ Q x.
  Proof.
    intros ? ? ? ? ?; rewrite <- Sum_Pred_negR; auto.
  Qed.

  (* This invert our hypotheses *)
  (* YZ: TODO: There's probably a way to declare hints to invert hypotheses/apply lemmas in contexts *)
  Ltac invert_context :=
    repeat (match goal with
            | h: (_ +' _) _ |- _ => inv h
            | h: (_ +'' _) _ _ |- _ => inv h
            | h: (_ ∪ _) _ _ |- _ => inv h
            | h: (_ ->' _) _ _ |- _ => inv h
            | h: inl_ _ _ |- _ => inv h
            | h: inr_ _ _ |- _ => inv h
            | h: ~ (_ +' _) (inl _) |- _ => apply Sum_Pred_negL_forward in h
            | h: ~ (_ +' _) (inr _) |- _ => apply Sum_Pred_negR_forward in h
            end).

  (* This should be moved to Utils, it tells auto that it can use the constructors of these inductive to solve goals *)
  Hint Constructors Sum_Pred Inr_Pred Inl_Pred Sum_Rel Join_Rel Prod_Pred_to_Rel.

  (* The solver reduces, destruct the expressions that are patterned matched on, unfold [P] to make the negations apparent, invert the context and finally calls auto.
     TODO: We should define a Hint DB to reason about these predicates rather than explicitly rely on [auto using].
   *)
  Ltac solver :=
    cbn;
    repeat flatten_all;
    unfold P in *; cbn in *; intros;
    invert_context;
    auto using Sum_Pred_negL_backward, Sum_Pred_negR_backward.

  Lemma currying' : forall (A B C : Arena),
      exists (f : @M A + (@M B + @M C) -> (@M A + @M B) + @M C),
        @arena_isomorphism  (Arrow_Arena A (Arrow_Arena B C)) (Arrow_Arena (Prod_Arena A B) C) f.
  Proof.
    intros A B C.
    exists iso_curry; unfold arena_isomorphism, bijection.
    split.
    - apply iso_curry_bij.
    - intros [] []; cbn; intuition; solver.
      (* YZ: Mmmh in one case two constructors can apply, and we need to pick the second one :( *)
      constructor.
      constructor.
      right.
      constructor; auto.
  Qed.

Section Plays.

  (*Context {A: Arena}.*)

  Definition pointer (M : Type) : Type := M * nat.

  Definition pointer_sequence (M : Type) := list (pointer M).

  (* A play is a pointer_sequence such that the first pointer is an initial
     move, and every subsequent pointer is such that its move is indeed enabled
     by the pointed justifying move *)

  Definition decreasing (f : nat -> nat) : Prop :=
    forall n, f n = 0 \/ f n < n.

  Inductive pointer_sequence_wf {M : Type} : pointer_sequence M -> Prop :=
   | nil_wf : pointer_sequence_wf []
   | cons_wf (p: pointer_sequence M) (Hp : pointer_sequence_wf p) (m : M) (n : nat) (Hn : n = 0 \/ n < length p)  :
       pointer_sequence_wf ((m,n) :: p).


  Fixpoint extract_points_to_fun {M : Type} (p : pointer_sequence M) : nat -> nat :=
    match p with
    | [] => fun _ => 0
    | h :: t => let f := extract_points_to_fun t in
                let (m,n) := h in
                fun x => if x =? length p then n else f x end.
  (*there might be an issue with self pointing*)
  Lemma extract_gt_length : forall (M : Type) (p : pointer_sequence M) (k : nat),
      k > length p -> extract_points_to_fun p k =0.
    Proof.
      intros. induction p; simpl; auto.
      destruct a. simpl in H. destruct (k =? S (length p)) eqn : Heq.
      - apply Nat.eqb_eq in Heq. omega.
      - apply IHp. omega.
    Qed.

  Lemma wf_points_to_dec : forall (M : Type) (p : pointer_sequence M), pointer_sequence_wf p ->
                                                                       decreasing (extract_points_to_fun p).
    Proof.
      intros. induction H.
      - simpl. unfold decreasing. intros. auto.
      - simpl. unfold decreasing. intros. destruct n0 as [ | x]; auto.
        + left. destruct ( 0 =? S (length p)) eqn : Heq; try discriminate.
          unfold decreasing in *. specialize ( IHpointer_sequence_wf 0); omega.
        + unfold decreasing in *.  specialize (IHpointer_sequence_wf (S x)).
          destruct IHpointer_sequence_wf as [H0  | H0]; destruct Hn.
          * rewrite H0. rewrite H1. left. destruct  (S x =? S (@length (pointer M0) p)); auto.
          * rewrite H0. right. destruct  (S x =? S (@length (pointer M0) p)) eqn : Heq; try omega.
            apply Nat.eqb_eq in Heq. omega.
          * rewrite H1. right. destruct ( S x =? S (@length (pointer M0) p)); auto; omega.
          * right. destruct ( S x =? S (@length (pointer M0) p)) eqn : Heq; try omega.
            apply Nat.eqb_eq in Heq. omega.
    Qed.


    Lemma dec_points_to_cons : forall (M : Type) (m : M) (n : nat) (p : pointer_sequence M),
        decreasing (extract_points_to_fun ((m,n) :: p)) -> decreasing (extract_points_to_fun p).
      Proof.
        induction p.
        - simpl. unfold decreasing. intros; left; auto.
        -
      Admitted.

    Lemma dec_points_to_wf : forall (M : Type) (p : pointer_sequence M), decreasing (extract_points_to_fun p) ->
                                                                         pointer_sequence_wf p.
      Proof.
        intros. induction p.
        - constructor.
        - destruct a as [m n]. apply cons_wf.
          + apply IHp. simpl in H. clear IHp. unfold decreasing in *. intros k. specialize (H k).
            destruct H; destruct (k =? S (length p)) eqn : Heq; try tauto.
            * apply Nat.eqb_eq in Heq. left. apply extract_gt_length. omega.
            * apply Nat.eqb_eq in Heq. left. apply extract_gt_length. omega.
          + apply dec_points_to_cons in H as H1. unfold decreasing in H1, H. simpl in H.
            specialize (H n).
            destruct (n =? S (length p)) eqn : Heq.
            * destruct H; omega.
            * fold decreasing in H1.

            simpl in H. unfold decreasing in H.
           (* specialize (H1 n (length p)). destruct H1; auto.


              enough (pointer_sequence_wf p).
              -- inv H1.
                 ++ specialize (H n). rewrite Heq in H.
                    d
                    simpl in H0. simpl in H. simpl. specialize (H n).
                    destruct (n =? 1); destruct H; try omega.
                    ** left.

            unfold decreasing in H. right.

            simpl in H. specialize (H n) as H'.
            destruct (n =? S (length p)) eqn : Heq.
            * apply Nat.eqb_eq in Heq. destruct H'; omega.
            * assert (decreasing (extract_points_to_fun p)). admit. apply IHp in H1.
              -- clear H'. clear H0. simpl in H. specialize (H n). simpl in Heq. rewrite Heq in H.
              destruct H.
              -- omega.*)
      Admitted.

  Record play (A : Arena) (p: pointer_sequence M): Prop :=
    {
      play_justifies: forall p' (m: M) (a: nat),
        snoc p' (m,a) ⊑ p -> p' <> [] ->
        exists q b, Q q /\ p'[[a]] = Some (q,b) /\ q ⊢ m;

      play_init: forall (q: M) (a: nat), [(q,a)] ⊑ p -> I q
    }.

  (*Lemma play_prefix_closed*)

  Definition strategy (A : Arena) := pointer_sequence M -> Prop.

  (* A strategy is a set of plays that is closed both by prefixed and by legal O-moves *)
  (* Note: traditional presentations only contain the even-lengthed ones contained here *)
  Record strategy_wf (A : Arena) (s: strategy A): Prop :=
    {
      are_plays: forall p, s p -> play A p;
      prefix_closed: forall p p', s p -> p' ⊑ p -> s p';
      Oclosed: forall p m, s p -> play A (snoc p m) -> O (fst m) -> s (snoc p m)
    }.

  (* Alternatively, strategies can be defined by a next move function *)
  Definition next_move (A : Arena) := pointer_sequence M -> (pointer M -> Prop).

  Definition next_move_wf (A : Arena) (s: next_move A): Prop :=
    forall p m a, play A p -> s p (m,a) -> play A (snoc p (m,a)).

  Inductive strategy_from_next_move (A : Arena) (next: next_move A): strategy A :=
  | Empty_play: strategy_from_next_move A next []
  | P_move: forall p m a,
      strategy_from_next_move A next p ->
      next p (m,a) ->
      strategy_from_next_move A next (snoc p (m,a))
  | O_move: forall p m a,
      O m ->
      strategy_from_next_move A next p ->
      play A (snoc p (m,a)) ->
      strategy_from_next_move A next (snoc p (m,a)).
  Hint Constructors strategy_from_next_move.

  Lemma nil_is_play: forall A, play A [].
  Proof.
    split; intros.
    - inv H; exfalso; eauto.
    - inv H; exfalso; eauto.
  Qed.
  Hint Resolve nil_is_play.

  Lemma strategy_from_next_move_wf:
    forall A next, next_move_wf A next ->
            strategy_wf A (strategy_from_next_move A next).
  Proof.
    intros A next nextWF; split.
    - induction p as [| [m a] p IH] using rev_ind; auto.
      intros ?.
      inv H.
      + exfalso; eauto.
      + apply nextWF; auto.
        apply snoc_inj in H0; destruct H0; subst; auto.
      + apply snoc_inj in H0; destruct H0; subst; auto.
    - intros p p' strat; revert p'; induction strat; intros p' prefix.
      + inv prefix; auto.
      + apply prefix_snoc in prefix; destruct prefix as [-> | ?]; auto.
      + apply prefix_snoc in prefix; destruct prefix as [-> | ?]; auto.
    - intros p m strat; revert m; induction strat; intros [] PLAY HO; auto.
  Qed.

  (* Least strategy spanned by a set of plays.
     TODO: think about this for a more interesting definition.
   *)
  Record least_strat (A : Arena) (generators: pointer_sequence M -> Prop) (s: strategy A): Prop :=
    {
      generators_plays: forall p, generators p -> play A p;
      s_strategy: strategy_wf A s;
      s_least_strategy: forall s', strategy_wf A s' -> generators ⊆ s' -> s ⊆ s'
    }.

  Fixpoint deletion (A : Arena) (p: pointer_sequence M): pointer_sequence M :=
    match view p with
    | Nil => []
    | Snoc x p => []
    end.


  Notation "x <? y" := (Nat.ltb x y) (at level 70).
  Definition redirect (n : nat) (f : nat -> nat) : nat -> nat :=
    fun m => if f m =? n then f n (*follow the link*)
             else if n <? f m then f m - 1 (*reindex*)
             else f m. (* no change needed*)

  Lemma decreasing_zero : forall f, decreasing f -> f 0 = 0.
    Proof.
      intros. unfold decreasing in *. specialize (H 0).
      destruct H; auto. omega.
    Qed.

  Lemma redirect_pres_decrease : forall f n, decreasing f -> decreasing (redirect n f).
  Proof.
    specialize (Nat.eqb_eq) as Hnat.
    unfold decreasing in *. intros f n Hdec m. intros.
    unfold redirect.
    destruct (f m =? n) eqn: Hfmn.
    - apply Hnat in Hfmn. rewrite <- Hfmn.
      specialize (Hdec (f m)) as Hfm. destruct Hfm; try tauto.
      specialize (Hdec m) as Hm. destruct Hm; omega.
    - specialize (Nat.eqb_neq) as Hnat'. clear Hfmn.
      destruct (n <? f m) eqn : Hfmn.
      + specialize (Hdec m). destruct Hdec; omega.
      + apply Hdec.
   Qed.

  (** definitely wrong  *)
  Definition decr_above_or_eq (n : nat) (f : nat -> nat) :=
    fun m => if Nat.ltb n m then f m - 1 else f m.

  Fixpoint delete_fun {M : Type} (p : pointer_sequence M) (X : M -> bool) : pointer_sequence M * (nat -> nat) :=
    match p with
    | [] => ([], fun x => x)
    | x :: p => let (m,n) := x in
                  let (p',f) := delete_fun p X in
                  if X m
                  then (p', redirect (length p + 1) f )
                  else (x :: p',f) end.

  Fixpoint delete {M : Type} (p : pointer_sequence M) (X : M -> bool) : pointer_sequence M :=
    let (p',f) := delete_fun p X in
    map (fun x => match x with pair m n => (m, f n) end) p'.

  Lemma delete_fun_delete_same_m : forall (M : Type) (p : pointer_sequence M) (X : M -> bool),
      map fst (fst (delete_fun p X)) = map fst (delete p X).
    Proof.
      intros. induction p; auto.
      simpl. destruct a eqn : Heqa. destruct (delete_fun p X) eqn : Heqdel.
      destruct (X m) eqn: Hm; simpl.
      - simpl in *. clear Hm Heqa Heqdel IHp.
        induction p0; auto. simpl. rewrite <- IHp0. destruct a0. simpl. auto.
      - clear Hm Heqa Heqdel IHp.
         enough (map fst p0 = map fst (map (fun x : M0 * nat => let (m0, n1) := x in (m0, n0 n1))
          p0)). rewrite H. auto.
         induction p0; auto. simpl. destruct a0. simpl. rewrite IHp0. auto.
    Qed.


  Lemma delete_fun_none_in_X : forall (M : Type) (p : pointer_sequence M) (X : M -> bool),
     Forall (fun x => X (fst x) = false) (fst (delete_fun p X)).
  Proof.
    intros. induction p.
    - simpl. auto.
    - simpl. destruct a as [m n]. destruct (delete_fun p X) as [p' f] eqn : Heq.
      destruct (X m) eqn : Hx.
      + simpl in *. auto.
      + simpl in *. constructor; auto.
  Qed.


  Lemma delete_none_in_X : forall (M : Type) (p : pointer_sequence M) (X : M -> bool),
      Forall (fun x => X (fst x) = false) (delete p X).
  Proof.
    intros.
    enough (Forall (fun m => X m = false) (map fst (delete p X))).
    - induction (delete p X); auto. inv H. constructor; auto.
    - rewrite <- delete_fun_delete_same_m.
      induction p; simpl; auto. destruct a as [m n]. destruct (delete_fun p X) as [p' f] eqn : Heq.
      destruct (X m) eqn : Hx; simpl in *; auto.
  Qed.

(*  Lemma delete_preserves_play_init : forall (A : Arena) (p : pointer_sequence M) (X : M -> bool),
      play *)
(** doesn't hold in general*)
(*delete partially preserves pointer structure in the sense that if a -> b, neither a nor b in X, then still a-> b
  also need some notion of the first valid ptr from a, where if
*)
(*
  Lemma delete_fun_predecreasing : forall (A : Arena) m n (p : pointer_sequence M) (X : M -> bool),
      decreasing (snd (delete_fun A ((m,n) :: p) X)).
    Proof.
      intros A m n p X. induction p.
      - simpl. unfold decreasing. intros.
        destruct (X m); simpl. unfold redirect.
        (* this may be related to a broader problem may need to make delete_fun [] return fun x => 0 *) admit.
      - simpl. destruct a. destruct (delete_fun A p X) eqn : Heq. simpl in *. rename n0 into f.
        destruct (X m); simpl; auto.
        apply redirect_pres_decrease. auto.
    Admitted.
*)
  Lemma delete_preserve_wf : forall (A : Arena) (p : pointer_sequence M) (X : M -> bool),
      pointer_sequence_wf p -> pointer_sequence_wf (delete p X).
  Proof.
    intros. induction H.
    - simpl. constructor.
    - simpl. destruct (X m) eqn : Hx.
      + destruct (delete_fun p X) eqn : Heq.
        destruct ( (map
       (fun x : M * nat =>
        let (m0, n1) := x in (m0, redirect (length p + 1) n0 n1)) p0)) eqn : Heq'.
        * constructor.
        * destruct p1. constructor.
  Admitted.

  Fixpoint first_n {A : Type} (n : nat) (l : list A) :=
    match n with
    | 0 => []
    | S m => match l with
             | [] => []
             | h :: t => h :: first_n m t end end.
(* need to deal with strict decreasing
  Fixpoint first_valid_ptr (A : Arena) (p :pointer_sequence M) (X : M -> bool) : option (pointer M) :=
    match p with
    | [] => None
    | h :: t => let (m,n) := h in
                if X m then first_valid_ptr A (first_n n t) X
                       else Some (m,n) end.
*)

Inductive first_valid_ptr_from (A : Arena) (p : pointer_sequence M) (X : M -> Prop) : M -> M -> Prop :=
  | m_valid (m : M) : ~ (X m) -> first_valid_ptr_from A p X m m

.


(** this lemma is false  *)
  Lemma delete_preserves_play : forall (A : Arena) (p : pointer_sequence M) (X : M -> bool),
      play A p -> play A (delete p X).
  Proof.
    intros. induction p; auto.
    simpl.
    Admitted.


(**Not sure this preserves play requirements*)
  Inductive delete_rel (A : Arena): pointer_sequence M -> pointer_sequence M -> (M -> Prop) -> (nat -> nat) -> Prop :=
    | del_nil (P : M -> Prop) : delete_rel A nil nil P (fun x => x)
    | del_snoc_in (p p' : pointer_sequence M) (P : M -> Prop) (m : M) (Hm : P m) (n : nat) (f : nat -> nat)
                  (Hpp' :delete_rel A p' p P f) : delete_rel A p' (snoc p (m,n)) P (redirect (length p') f)
    | del_snoc_out (p p' : pointer_sequence M) (P : M -> Prop) (m : M) (Hm : ~ P m) (n : nat) (f : nat -> nat)
                   (Hpp' : delete_rel A p' p P f) : delete_rel A (snoc p' (m,n)) (snoc p (m,n)) P f
.



  Definition name_set := nat -> bool.
  Definition empty : name_set := fun x => false.
  Definition add_elem x (s : name_set) := fun y => if Nat.eqb x y then true else s y.
  Definition contains (s : name_set) x := s x.
  Definition union (s t : name_set) := fun x => orb (s x)  (t x).

  Fixpoint hered_just_fun {M : Type} (p : pointer_sequence M ) (X : M -> bool) : pointer_sequence M * name_set :=
    match p with
    | [] => ([], empty)
    | x :: p => let (m,n) := x in
                let (p', s) := hered_just_fun p X in
                if X m
                then (x :: p', add_elem (length p) s)
                else (p',s)
    end.

  Definition hered_just {M : Type} (p : pointer_sequence M) (X : M -> bool) : pointer_sequence M :=
    fst (hered_just_fun p X).

  Inductive hered_just_rel (A : Arena) : pointer_sequence M -> pointer_sequence M -> (M -> Prop) -> (nat -> Prop) -> Prop :=
    | hered_nil (P : M -> Prop) : hered_just_rel A [] [] P (fun x => False)
    | hered_snoc_in (p p' : pointer_sequence M ) (P : M -> Prop) (m : M) (Hm : P m) (n : nat) (S : nat -> Prop)
                    (Hpp' : hered_just_rel A  p' p P S) : hered_just_rel A (snoc p' (m,n)) (snoc p (m,n)) P
                                                                      (fun x => S x \/ x = length p)
    | hered_snoc_out (p p' : pointer_sequence M) (P : M -> Prop) (m : M) (Hm : ~ P m) (n : nat) (S : nat -> Prop)
                    (Hpp' : hered_just_rel A p' p P S) : hered_just_rel A p' (snoc p (m,n)) P S
  .


End Plays.


Section Composition.
  Lemma Forall_tail : forall (A : Type) (P : A -> Prop) (a : A) (l : list A), Forall P (a :: l) -> (P a /\ Forall P l).
  Proof.
    intros. inv H; auto.
  Qed.

  Definition list_subset_project (A : Type) (P : A -> Prop) (l : list A) (Hl : Forall P l) : list {a : A | P a}.
    induction l.
    - apply ([]).
    - apply Forall_tail in Hl as [Ha Ht]. remember (exist P a Ha). specialize (IHl Ht).
      apply (s :: IHl).
  Defined.

  Lemma preserve_elem : forall (A : Type) (P : A-> Prop) (l : list A) (Hl : Forall P l),
      map (fun x => match x with exist _ a _ => a end) (list_subset_project A P l Hl) = l.
  Proof.
    intros. induction l; auto.
    simpl.  destruct ( Forall_tail A0 P0 a l Hl). simpl. rewrite IHl. auto.
  Qed.

  Definition is_left {A B : Type} (x : A + B) :=
    match x with inl _ => True | inr _ => False end.

  Definition is_right {A B : Type} (x : A + B) :=
    match x with inl _ => False | inr _ => True end.

  Definition lower_union_list_left (A B: Type) (l : list (A + B)) (Hl : Forall is_left l) : list A.
    induction l.
    - apply [].
    - apply Forall_tail in Hl as [Ha Ht]. specialize (IHl Ht).
      unfold is_left in Ha. destruct a; try contradiction.
      apply (a :: IHl).
  Defined.

  Definition lower_union_list_right (A B : Type) (l : list (A + B)) (Hl : Forall is_right l) : list B.
    induction l.
    - apply [].
    - apply Forall_tail in Hl as [Ha Ht]. specialize (IHl Ht).
      unfold is_right in Ha. destruct a; try contradiction.
      apply (b :: IHl).
  Defined.

  Definition is_leftb {A B : Type} (x : A + B) :=
    match x with inl _ => true | inr _ => false end.

  Definition is_rightb {A B : Type} (x : A + B) :=
    match x with inl _ => false | inr _ => true end.

  Lemma is_left_iffb : forall (A B : Type) (x : A + B), is_left x <-> is_leftb x = true.
  Proof.
    intros A B x. split; intros; destruct x; simpl; auto; discriminate.
  Qed.

  Lemma is_right_iffb : forall (A B : Type) (x : A + B), is_right x <-> is_rightb x = true.
  Proof.
    intros A B x. split; intros; destruct x; simpl; auto; discriminate.
  Qed.


  Definition delete_left_lower {A B : Type} (l : pointer_sequence (A + B)) : pointer_sequence B.
    intros. remember (delete l is_leftb). remember (delete_none_in_X (A + B) l is_leftb).
    assert (Forall (fun x => is_right (fst x) ) p).
    {
      clear Heqf. rewrite <- Heqp in f. clear Heqp.
      induction p.
      - constructor.
      - inv f. constructor; auto.
        destruct a. simpl in *. destruct s; try discriminate; simpl; auto.
    }
    clear Heqp.
    induction (p).
    - apply [].
    - apply Forall_tail in H as [Ha Hp].
      apply IHp0. apply Hp.
  Defined.


  Definition delete_right_lower {A B : Type} (l : pointer_sequence (A + B)) : pointer_sequence A.
    intros. remember (delete l is_rightb) as p. remember (delete_none_in_X (A + B) l is_rightb).
    assert (Forall (fun x => is_left (fst x)) p).
    {
      clear Heqf. rewrite <- Heqp in f. clear Heqp.
      induction p.
      - constructor.
      - inv f. constructor; auto.
        destruct a. simpl in *. destruct s; try discriminate; simpl; auto.
    }
    clear Heqp.
    induction p.
    - apply [].
    - apply Forall_tail in H as [Ha Hp].
      apply IHp. apply Hp.
  Defined.


  Definition interaction (M N : Type) (tau : pointer_sequence M -> Prop) (sigma : pointer_sequence N -> Prop)
             : pointer_sequence (M + N) -> Prop :=
    fun p => tau (delete_right_lower p) /\ sigma (delete_left_lower p).


  Definition iteration (M : Type) (N : M -> bool) (sigma : pointer_sequence M -> Prop) : pointer_sequence M -> Prop  :=
    fun p => forall (m : M) (n : nat), In (m,n) p -> N m = true -> sigma (hered_just p N) .

(*
  Definition composition (A B C : Type) ()
*)
End Composition.
