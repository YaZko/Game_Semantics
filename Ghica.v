From Games Require Import
     Utils.

From Coq Require Import
     List
     Relations.
Import ListNotations.

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
  forall x y, x = y <-> f x = f y. 

Definition arena_isomorphism {A1 A2 : Arena} (f : @M A1 -> @M A2) : Prop :=
  bijection f /\ forall m n, (@Q A1 m <-> @Q A2 (f m)) /\ (@O A1 m <-> @O A2 (f m)) /\
                 (@I A1 m <-> @I A2 (f m)) /\ (@enable A1 m n <-> @enable A2 (f m) (f n)).

Definition isomorphic (A1 A2 : Arena) : Prop := exists f, @arena_isomorphism A1 A2 f.

Lemma iso_reflexive : forall A, isomorphic A A.
Proof.
  intros. unfold isomorphic, arena_isomorphism. exists (fun x => x). 
  split.
  - unfold bijection. intros. split; auto.
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
  - intros. unfold bijection in *. apply Hbi12 in H. apply Hbi23 in H. auto.
  - intros. unfold bijection in *. apply Hbi23 in H. apply Hbi12 in H. auto.
Qed.


Definition isol {A : Arena} (m : void + M) : M :=
  match m with
  | inl v => match v return M with end
  | inr m' => m' end.

Definition isor {A : Arena} (m : M + void) : M :=
  match m with
  | inl m' => m'
  | inr v => match v return M with end
  end.


Lemma unit_left_id_product : forall (A : Arena), exists (f : void + M -> M),
      @arena_isomorphism (Prod_Arena Unit A) A f.
  Proof.
    intro A. exists isol. unfold arena_isomorphism, bijection. split.
    - intros. split; intros; subst; auto. destruct x; destruct y; 
       unfold isol in *; simpl in *; try contradiction. subst. auto.
    - intros. repeat split; intros;
      try (destruct m; try contradiction; simpl in *; inv H; try contradiction; auto);
      try (destruct m; try contradiction; simpl in *; constructor; assumption).
      destruct m; destruct n; try contradiction. simpl in *. constructor. assumption.
  Qed.

Lemma unit_right_id_product : forall (A : Arena), exists (f : M + void -> M),
        @arena_isomorphism (Prod_Arena A Unit) A f.
  Proof.
    intros A. exists isor. unfold arena_isomorphism, bijection. split.
    - intros. split; intros; subst; auto. destruct x; destruct y; 
       unfold isor in *; simpl in *; try contradiction. subst. auto.
    - intros. repeat split; intros;
      try (destruct m; try contradiction; simpl in *; inv H; try contradiction; auto);
      try (destruct m; try contradiction; simpl in *; constructor; assumption).
      destruct m; destruct n; try contradiction. simpl in *. constructor. assumption.
  Qed.

Lemma unit_left_id_exp : forall (A : Arena), exists (f : void + M -> M),
        @arena_isomorphism (Arrow_Arena Unit A) A f.
  Proof.
    intros A. exists isol. unfold arena_isomorphism, bijection. split.
    - intros. split; intros; subst; auto. destruct x; destruct y; 
       unfold isor in *; simpl in *; try contradiction. subst. auto.
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

(** could probably parts of automate this  *)
Lemma currying : forall (A B C : Arena), exists (f : @M A + (@M B + @M C) -> (@M A + @M B) + @M C),
                 @arena_isomorphism  (Arrow_Arena A (Arrow_Arena B C)) (Arrow_Arena (Prod_Arena A B) C) f.
  Proof.
    intros. exists iso_curry. unfold arena_isomorphism, bijection. split.
    - intros. split; intros.
      + subst. auto.
      + destruct x; destruct y; simpl in *; auto; try discriminate.
        * injection H. intros. subst. auto.
        * destruct m0; try discriminate.
        * destruct m; try discriminate.
        * destruct m; destruct m0; try discriminate;
            try (injection H; intros; subst; auto).
   - intros. repeat split; intros.
     + destruct m; simpl in *.
       * inv H. repeat constructor. auto.
       * inv H. inv H1; repeat constructor; auto.
     + destruct m; simpl in *; inv H; try (inv H1).
       * repeat constructor. auto.
       * destruct m; simpl in *; repeat constructor.
         -- injection H0. intros. discriminate.
         -- discriminate.
       * destruct m; simpl in *; repeat constructor.
         -- injection H0. intros. subst. auto.
         -- discriminate.
       * destruct m; try discriminate. injection H0. intros. subst. repeat constructor. auto.
     + destruct m; simpl in *. (** running into issues with the opponent construction ~OA + ~OB vs ~(OA + OB) ?  *)
       * inv H. constructor. unfold P in *. admit.
       * inv H. inv H1.
         -- constructor. unfold P in *. admit.
         -- constructor. auto.
     + destruct m; simpl in *.
       * inv H. constructor. auto. admit.
       * destruct m; simpl in *.
         -- constructor. inv H. constructor.
Admitted.       


Section Plays.

  (*Context {A: Arena}.*)

  Definition pointer (M : Type) : Type := M * nat.

  Definition pointer_sequence (M : Type) := list (pointer M).

  (* A play is a pointer_sequence such that the first pointer is an initial
     move, and every subsequent pointer is such that its move is indeed enabled
     by the pointed justifying move *)
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

  Definition decr_above_or_eq (n : nat) (f : nat -> nat) :=
    fun m => if Nat.ltb n m then f m - 1 else f m.

  Fixpoint delete_fun (A : Arena) (p : pointer_sequence M) (X : M -> bool) : pointer_sequence M * (nat -> nat) :=
    match p with
    | [] => ([], fun x => x)
    | x :: p => let (m,n) := x in 
                  let (p',f) := delete_fun A p X in
                  if X m 
                  then (p', decr_above_or_eq (length p + 1) f )
                  else (x :: p',f) end.

  Fixpoint delete (A : Arena) (p : pointer_sequence M) (X : M -> bool) : pointer_sequence M :=
    let (p',f) := delete_fun A p X in
    map (fun x => match x with pair m n => (m, f n) end) p'.

  Lemma delete_fun_delete_same_m : forall (A : Arena) (p : pointer_sequence M) (X : M -> bool),
      map fst (fst (delete_fun A p X)) = map fst (delete A p X).
    Proof.
      intros. induction p; auto.
      simpl. destruct a eqn : Heqa. destruct (delete_fun A0 p X) eqn : Heqdel.
      destruct (X m) eqn: Hm; simpl.
      - simpl in *. clear Hm Heqa Heqdel IHp.
        induction p0; auto. simpl. rewrite <- IHp0. destruct a0. simpl. auto.
      -  clear Hm Heqa Heqdel IHp. enough (map fst p0 = map fst (map (fun x : M * nat => let (m0, n1) := x in (m0, n0 n1))
          p0)). rewrite H. auto.
         induction p0; auto. simpl. destruct a0. simpl. rewrite IHp0. auto.
    Qed.


  Lemma delete_fun_none_in_X : forall (A : Arena) (p : pointer_sequence M) (X : M -> bool),
     Forall (fun x => X (fst x) = false) (fst (delete_fun A p X)).
  Proof.
    intros. induction p.
    - simpl. auto.
    - simpl. destruct a as [m n]. destruct (delete_fun A0 p X) as [p' f] eqn : Heq.
      destruct (X m) eqn : Hx.
      + simpl in *. auto.
      + simpl in *. constructor; auto.
  Qed.


  Lemma delete_none_in_X : forall (A : Arena) (p : pointer_sequence M) (X : M -> bool),
      Forall (fun x => X (fst x) = false) (delete A p X).
  Proof.
    intros.
    enough (Forall (fun m => X m = false) (map fst (delete A0 p X))).
    - induction (delete A0 p X); auto. inv H. constructor; auto.
    - rewrite <- delete_fun_delete_same_m.
      induction p; simpl; auto. destruct a as [m n]. destruct (delete_fun A0 p X) as [p' f] eqn : Heq.
      destruct (X m) eqn : Hx; simpl in *; auto.
  Qed.
      
  Lemma delete_preserves_play : forall (A : Arena) (p : pointer_sequence M) (X : M -> bool),
      play A p -> play A (delete A p X).
  Proof.
    intros. induction p; auto.

(**Not sure this preserves play requirements*)
  Inductive delete_rel (A : Arena): pointer_sequence M -> pointer_sequence M -> (M -> Prop) -> (nat -> nat) -> Prop := 
    | del_nil (P : M -> Prop) : delete_rel A nil nil P (fun x => x)
    | del_snoc_in (p p' : pointer_sequence M) (P : M -> Prop) (m : M) (Hm : P m) (n : nat) (f : nat -> nat)
                  (Hpp' :delete_rel A p' p P f) : delete_rel A p' (snoc p (m,n)) P (decr_above_or_eq (length p') f)
    | del_snoc_out (p p' : pointer_sequence M) (P : M -> Prop) (m : M) (Hm : ~ P m) (n : nat) (f : nat -> nat)
                   (Hpp' : delete_rel A p' p P f) : delete_rel A (snoc p' (m,n)) (snoc p (m,n)) P f
.


  
  Definition name_set := nat -> bool.
  Definition empty : name_set := fun x => false.
  Definition add_elem x (s : name_set) := fun y => if Nat.eqb x y then true else s y.
  Definition contains (s : name_set) x := s x.
  Definition union (s t : name_set) := fun x => orb (s x)  (t x).

  Fixpoint hered_just_fun (A : Arena) (p : pointer_sequence M ) (X : M -> bool) : pointer_sequence M * name_set :=
    match p with
    | [] => ([], empty)
    | x :: p => let (m,n) := x in
                let (p', s) := hered_just_fun A p X in
                if X m
                then (x :: p', add_elem (length p) s)
                else (p',s)
    end.

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

End Composition.

 
