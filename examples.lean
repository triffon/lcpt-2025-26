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

theorem ConjunctionIsCommutative2 : A ∧ B → B ∧ A := by
  intro ⟨hA, hB⟩
  exact ⟨hB, hA⟩

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
variable (drinks : bar -> Prop)

theorem drinkersParadox (drunkard : bar) : ∃ x, drinks x → ∀ y, drinks y :=
  Stab (fun notDrinkersParadox =>
        (notDrinkersParadox
          (Exists.intro drunkard (fun _ y =>
            (Stab (fun notDrinksY => (notDrinkersParadox
              (Exists.intro y (fun drinksY => (False.elim (notDrinksY drinksY)))))))))))

theorem drinkersParadoxClassical (drunkard : bar) : ∃ x, drinks x → ∀ y, drinks y := by
  -- We start by splitting the world into two classical possibilities:
  -- Either everyone drinks, or not everyone drinks.
  by_cases h : ∀ y, drinks y

  · -- CASE 1: Everyone in the bar drinks.
    -- Since the bar isn't empty (we know `drunkard` is there), we can pick anyone.
    -- We choose the `drunkard` as our witness.
    exists drunkard

    -- We need to prove: drinks drunkard → ∀ y, drinks y
    -- So, we assume the drunkard drinks.
    intro _

    -- We must prove everyone drinks.
    -- But we already assumed that in this case (`h`), so we just use it exactly.
    exact h

  · -- CASE 2: Not everyone drinks.
    -- Classically, "not everyone drinks" means "there exists someone who does not drink."
    have h_exists : ∃ y, ¬ drinks y := Classical.not_forall.mp h

    -- Let's extract that specific person. Let `p` be the person,
    -- and `hp` be the proof that they don't drink.
    have ⟨p, hp⟩ := h_exists

    -- We pick this specific non-drinking person `p` as our witness!
    exists p

    -- We need to prove: drinks p → ∀ y, drinks y
    -- We start by assuming `p` drinks.
    intro hp_drinks

    -- This creates a logical explosion. `hp_drinks` says `p` drinks,
    -- but `hp` says `p` does not drink.
    -- Since a false premise implies anything, the proof is complete.
    contradiction

