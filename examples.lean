variable (A B C : Prop)

theorem ITerm : A → A := fun (u : A) => u

theorem I : A → A := by
  intro u
  apply u

#check I
#print I

theorem K : A → B → A  := by
  intro u v
  apply u

theorem S : (A → B → C) → (A → B) → A → C := by
  intro u v w
  apply u
  . apply w
  . apply v
    apply w

#check And
#print And

theorem ConjunctionIsCommutative : A ∧ B → B ∧ A := by
  intro u
  cases u with
  | intro v w => apply And.intro
                 . apply w
                 . apply v

theorem DisjunctionIsCommutative : A ∨ B → B ∨ A := by
  intro u
  cases u with
  | inl v => right; exact v
  | inr w => left;  exact w

axiom Stab : ∀ {A : Prop}, ¬¬A → A

theorem LEM : A ∨ ¬A := by
  apply Stab; intro u
  apply u
  right
  intro v
  apply u
  left
  exact v

variable (A : Nat → Prop)

theorem ForallImpliesExists : (∀ x, A x) → (∃ x, A x) := by
  intro u
  exists 0
  apply u

variable (bar : Type)
variable (drunkard : bar)
variable (drinks : bar -> Prop)

theorem drinkersParadox : ∀ (drunkard : bar), ∃ x, drinks x → ∀ y, drinks y :=
  fun drunkard => Stab (fun notDrinkersParadox =>
                         (notDrinkersParadox
                           (Exists.intro drunkard (fun _ y =>
                             (Stab (fun notDrinksY => (notDrinkersParadox
                                (Exists.intro y (fun drinksY => (False.elim (notDrinksY drinksY)))))))))))
