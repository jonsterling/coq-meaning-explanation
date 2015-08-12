Inductive 𝔻 : Type :=
  pair : 𝔻 -> 𝔻 -> 𝔻
| fst : 𝔻 -> 𝔻
| snd : 𝔻 -> 𝔻
| ax : 𝔻
| unit : 𝔻.

Inductive judgment : Type :=
  eq : 𝔻 -> 𝔻 -> 𝔻 -> judgment
| prop : 𝔻 -> judgment
| ver : 𝔻 -> judgment
| eval : 𝔻 -> 𝔻 -> judgment
| hyp : judgment -> judgment -> judgment.

Notation "M = N ∈ A" := (eq A M N) (at level 100).
Notation "M ⇓ N" := (eval M N) (right associativity, at level 60).
Notation "N ⇐ M" := (hyp M N) (right associativity, at level 60).

Open Scope core_scope.

Module Meaning.
  Record t : Type := 
    {presupposition : Type;
     meaning : presupposition -> Type}.
End Meaning.

Module Evidence.
  Record t (m : Meaning.t) : Type :=
    {presupposition : Meaning.presupposition m;
     meaning : Meaning.meaning m presupposition}.
End Evidence.

Module PER.
  Record t (D : Type) : Type :=
    {relation : D -> D -> Type;
     symmetric : forall M N, relation M N -> relation N M;
     transitive : forall M N O, relation M N -> relation N O -> relation M O}.
End PER.

Inductive evals : 𝔻 -> 𝔻 -> Type :=
  pairCanon : forall {M N}, evals (pair M N) (pair M N)
| axCanon : evals ax ax
| unitCanon : evals unit unit
| fstEval : forall {MN M N M'}, evals MN (pair M N) -> evals M M' -> evals (fst MN) M'
| sndEval : forall {MN M N N'}, evals MN (pair M N) -> evals N N' -> evals (snd MN) N'.

Hint Resolve pairCanon axCanon fstEval sndEval unitCanon.


Inductive unitRelation : 𝔻 -> 𝔻 -> Type :=
  unitAx : unitRelation ax ax.

Hint Resolve unitAx.

Ltac invert_unitRelation :=
  match goal with
    [H : unitRelation _ _ |- _] => inversion H; clear H
  end.

Theorem unitPer : PER.t 𝔻.
Proof.
  split with unitRelation; intuition;
  repeat invert_unitRelation; eauto.
Defined.

Fixpoint denotes (A : 𝔻) (R : PER.t 𝔻) : Type :=
  match A with
    unit => R = unitPer
  | _ => False
  end.

Open Scope type_scope.

Definition isProp (P : 𝔻) :=
  {P' : 𝔻 & evals P P' & { R : PER.t 𝔻 & denotes P' R}}.

Fixpoint presupposition (J : judgment) : Type :=
  match J with
    relates A M N => isProp A
  | eq A M N => isProp A
  | ver A => isProp A
  | hyp J1 J2 => presupposition J1 * presupposition J2
  | _ => True
  end.

Fixpoint meaning (J : judgment) : presupposition J -> Type.
Proof.
  induction J.

  (* M ~ N @ A *)
  + intro p; destruct p as [P' _ [[R _ _] _]].
    exact {M : 𝔻 & {N : 𝔻 & (evals 𝔻0 M * evals 𝔻1 N) & R M N }}.

  (* A prop *)
  + intro p; exact (isProp 𝔻0).

  (* A ver *)
  + intro p; destruct p as [P' _ [[R _ _] _]].
    exact {M : 𝔻 & R M M}.
    
  (* M ⇒ N *)
  + intro p; exact (evals 𝔻0 𝔻1).

  (* J2 (J1) *)
  + intro p; destruct p as [p1 p2].
    exact (IHJ1 p1 -> IHJ2 p2).
Defined.

Definition evident (J : judgment) : Type :=
  {p : presupposition J & meaning J p}.

Notation "⊨ J" := (evident J) (right associativity, at level 90).

Lemma test : ⊨ fst (pair ax ax) ⇓ ax.
Proof.
  compute; eauto.
Qed.


Ltac invert_evals :=
  match goal with
    [H : evals _ _ |- _] => inversion H
  end.


Lemma welp : ⊨ (fst ax ⇓ ax) ⇐ (ax ⇓ pair ax ax).
Proof.
  compute; split with (I, I); intro.
  invert_evals.
Qed.

Lemma unitIsProp : ⊨ prop (fst (pair unit ax)).
Proof.
  compute; split; eauto.
Qed.
