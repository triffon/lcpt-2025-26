Import Coq.Init.Nat.

Section Example.
  Check 0.
  Check S.
  Check nat.
  Print nat.
  Check Set.
  Check Type.
  Variable n : nat.
  Check n.
  Print n.
  Check n + 2.
  Check fun n => n + 2.
  Definition plus2 := fun (n : nat) => n + 2.
  Check plus2.
  Print plus2.
  Check 2 + 2.
  Compute 2 + 2.
  Check plus2 2.
  Compute plus2 2.
  Check n > 2.
  Check Prop.
  Definition myconj (A B : Prop) := forall (X : Prop), ((A -> B -> X) -> X).
  Check myconj.
  Definition myConjSet (A B : Set) := forall (X : Set), ((A -> B -> X) -> X).
  Check myConjSet.
  Compute n > 2.
  Check lt n 3.
  Check lt.
  Print lt.
  Check le.
  Print le.
  Compute 2 <= 3.
  Print bool.
  Fixpoint lefun (m n : nat) :=
     match n with
      | 0 => match m with
              | 0 => true
              | S m' => false
            end
      | S n' => match m with
                | 0 => true
                | S m' => lefun m' n'
               end
    end.
  Compute lefun 2 3.
  Compute lefun 3 2.
  Check 2 <? 3.
  Check lefun.
  Check le.
  Compute 2 <= 3.
  Lemma twole4 : 2 <= 4.
    auto.
  Qed.
  Check twole4.
  Print twole4.
  Print le.
End Example.

Section PropMinLog.
  Variable A : Prop.
  Goal A -> A.
    intro u.
    apply u.
    Show Proof.
  (* Qed. *)
  Save Identity.
  Check Identity.
  Print Identity.
  Definition IdentityTerm : A -> A := fun (u : A) => u.
  Check IdentityTerm.
  Print IdentityTerm.

  Variable B : Prop.
  Lemma K : A -> B -> A.
    intros u v.
    apply u.
  Qed.
  Print K.

  Definition KTerm : A -> B -> A := fun (u : A) (v : B) => u.
  Print KTerm.

  Variable C : Prop.
  Lemma S : (A -> B -> C) -> (A -> B) -> A -> C.
    intros u v w.
    apply u.
    apply w.
    apply v.
    apply w.
  Qed.

  Lemma S2 : (A -> B -> C) -> (A -> B) -> A -> C.
    intros u v w.
    apply u; [ assumption | apply v; assumption ].
  Qed.
  Print S.
  Print S2.

  Definition STerm : (A -> B -> C) -> (A -> B) -> A -> C :=
    fun u v w => u w (v w).
  Print STerm.

  Check and.
  Print and.
  Check and A B.
  Lemma ConjunctionIsCommutative : A /\ B -> B /\ A.
    intro u.
    split.
      apply u.
      apply u.
  Qed.

  Print ConjunctionIsCommutative.

  Print and_ind.

  Definition ConjunctionIsCommutativeTerm : A /\ B -> B /\ A :=
    fun u : A /\ B => conj
                   (match u with | conj v w => w end)
                   (match u with | conj v w => v end).

  Print ConjunctionIsCommutativeTerm.

  Check or.
  Print or.

  Lemma DisjunctionIsCommutative : A \/ B -> B \/ A.
    intro u.
    elim u.
      intro v.
      right.
      assumption.

      (* аналогично *)
      intro w.
      left.
      assumption.
  Qed.

  Print or_ind.

  Print DisjunctionIsCommutative.

End PropMinLog.

Section PropClassLog.
  Hypothesis Stab : forall (A : Prop), ~~A -> A.
  Variable A : Prop.
  Check ~A.
  Check not.
  Print not.
  Check False.

  Lemma LEM : A \/ ~A.
    apply Stab; intro u.
    apply u.
    right.
    intro v.
    apply u.
    left.
    assumption.
  Defined.

  Print LEM.
  Compute LEM.
End PropClassLog.

Section PropIntLog.
  Variable A B : Prop.
  Lemma Task : (~~A -> ~~B) -> ~~(A -> B).
  (* tauto. *)
    intros u v.
    apply u.
      (* goal 1 *)
      intro w.
      apply v.
      intro a.
      exfalso; apply w; assumption.
      (* goal 2 *)
      intro w.
      apply v.
      intro; assumption.
  Defined.

  Print Task.
End PropIntLog.

Section PredMinLog.
  Variable α : Set.
  Variable A : α -> Prop.
  Variable x : α.
  Check A x.

  Lemma ForallImpliesExists : (forall x, A x) -> exists x, A x.
    intro u.
    exists x.
    apply u.
  Defined.

  Print ForallImpliesExists.

  Print ex.

  Variable R : α -> α -> Prop.

  Hypothesis RIsSymmetric  : forall x y, R x y -> R y x.
  Hypothesis RIsTransitive : forall x y z, R x y -> R y z -> R x z.
  Hypothesis RIsTotal : forall x, exists y, R x y.

  Theorem RIsReflexive : forall x, R x x.
    intro x0.
    (* знам, че ∃ y, така че R x0 y *)
    elim (RIsTotal x0); intros y Rx0y.
    apply RIsTransitive with (y := y).
      (* цел 1 *)
      assumption.

      (* цел 2 *)
      apply RIsSymmetric; assumption.
  Defined.

  Compute RIsReflexive.
End PredMinLog.

Section PredClassLog.
  Variable bar : Set.
  Variable drunkard : bar.
  Variable drinks : bar -> Prop.

  Hypothesis Stab : forall (A : Prop), ~~A -> A.

  Theorem drinkersParadox : exists x, drinks x -> forall y, drinks y.
    apply Stab; intro notDrinkersParadox.
    apply notDrinkersParadox.
    exists drunkard; intro drunkardDrinks.
    intro y.
    apply Stab; intro notDrinksY.
    apply notDrinkersParadox.
    exists y.
    intro drinksY.
    exfalso; apply notDrinksY; assumption.
  Qed.
End PredClassLog.
