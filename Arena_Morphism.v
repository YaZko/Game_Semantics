From Games Require Import
     Category
     Utils
     Arena.

Class is_morphism {A B : Arena} (f : @M A -> @M B) : Prop :=
  {
    respect_Q: forall m, Q m <-> Q (f m);
    respect_O: forall m, O m <-> O (f m);
    respect_I: forall m, I m <-> I (f m);
    respect_entail: forall m n, m ⊢ n <-> f m ⊢ f n;
  }.

Lemma morphism_preserves_WF (A B: Arena):
  forall f (surjective: forall b, exists a, b = f a),
    @is_morphism A B f -> @Arena_WF A -> @Arena_WF B.
Proof.
  intros f ? ?; constructor.
  - intros mb Imb.
    destruct (surjective mb) as [ma ->].
    eapply respect_I, init_WF in Imb.
    rewrite respect_Q,respect_O in Imb.
    auto.
  - intros mb nb Entail.
    destruct (surjective mb) as [ma ->], (surjective nb) as [na ->].
    eapply respect_entail, Q_entails in Entail.
    rewrite respect_Q in Entail.
    auto.
  - intros mb nb Entail.
    destruct (surjective mb) as [ma ->], (surjective nb) as [na ->].
    eapply respect_entail, alternating in Entail.
    rewrite 2 respect_O in Entail.
    auto.
  - intros mb nb Entail.
    destruct (surjective nb) as [na ->].
    destruct (surjective mb) as [ma ->].
    eapply respect_entail, non_init in Entail.
    rewrite respect_I in Entail; auto.
Qed.

Record ArenaM (A B : ArenaC): Type :=
  {
    f :> @M A -> @M B;
    morph: is_morphism f
  }.
Arguments morph {A B} _.

Definition morphism_id {A:Arena}: is_morphism (fun x => x).
Proof.
  split; try reflexivity.
Qed.

(** Identity function *)
Instance Id_Arena : Id_ ArenaM :=
  fun A => {| f := fun x => x ;
           morph := @morphism_id A |}.

Definition morphism_Initial {A: Arena} : @is_morphism Unit_Arena A (fun (x: void) => match x with end).
Proof.
  constructor; intuition; flatten_all.
Qed.

(* Over [ArenaM], the Unit_Arena is the initial element *)
Instance Initial_void : Initial ArenaM Unit_ArenaC :=
  fun A =>
    {|
      f := fun (x: @M Unit_ArenaC) => match x with end;
      morph := morphism_Initial
    |}.

