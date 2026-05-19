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
  Definition conj (A B : Prop) := forall (X : Prop), ((A -> B -> X) -> X).
  Check conj.
  Definition conjSet (A B : Set) := forall (X : Set), ((A -> B -> X) -> X).
  Check conjSet.
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
