/-
  Lean Tutorial — STUDENT WORKSHEET (synced)
  Part 0 — Foundations  ·  Part 1 — Cauchy–Schwarz  ·  Part 2 — Irrationality of √2
  Stack: Lean 4 + Mathlib.

  HOW TO USE
  ----------
  • Each `sorry` is one small subgoal; its statement is written in the
    `have … :` line, so you always know what to prove.
  • Hints live in the `-- HINT:` comments.
  • Replace every `sorry`. No `sorry` + no red squiggles = done.
  • Answer key: `tutorial_solutions.lean`.

  Rule of thumb used throughout:
    linarith → ordered-field inequalities (great over ℝ, fine for ℕ ≤/<)
    omega    → integer PARITY / divisibility / exact cancellation
-/
import Mathlib

namespace Tutorial

variable (P Q : Prop)

/- ========================================================================
   PART 0 — FOUNDATIONS
   ======================================================================== -/

/- 0.1  `rfl` and gentle arithmetic -/

-- MODEL (worked for you): `rfl` proves goals true by computation.
example : 2 + 2 = 4 := rfl

-- Exercise 0.1a.  HINT: `rfl` — `n + 0` reduces to `n` by definition.
example (n : ℕ) : n + 0 = n := by sorry

-- (FYI: `0 + n = n` is NOT `rfl`; it needs `Nat.zero_add n`. Try `rfl` to see it fail.)

-- Exercise 0.1b.  HINT: `norm_num`.
example : 17 * 23 = 391 := by sorry

/- 0.2  `rw` (rewrite with an equation) -/

-- Exercise 0.2a.  HINT: `rw [h]`.
example (a b : ℕ) (h : a = b) : a + 1 = b + 1 := by sorry

-- Exercise 0.2b.  HINT: `rw [← h]` (rewrite right→left).
example (a b : ℕ) (h : a = b) : b + 1 = a + 1 := by sorry

/- 0.3  `have` (prove a fact, then reuse it) -/

-- Exercise 0.3.  HINT: `have hsq : 0 ≤ x ^ 2 := sq_nonneg x`, then `linarith`.
example (x : ℝ) : 0 ≤ x ^ 2 + 1 := by sorry

/- 0.4  `rcases` (take things apart) -/

-- Exercise 0.4a.  HINT: `rcases h with ⟨hp, hq⟩`.
example (h : P ∧ Q) : P := by sorry

-- Exercise 0.4b.  HINT: `rcases h with hp | hq`, then `Or.inr` / `Or.inl`.
example (h : P ∨ Q) : Q ∨ P := by sorry

-- Exercise 0.4c — the `rfl | hpos` pattern (rehearsal for Part 2).
example (a : ℕ) (h : a ^ 2 = 0) : a = 0 := by
  rcases Nat.eq_zero_or_pos a with rfl | hpos
  · sorry                                   
  · exfalso
    have hpos2 : 0 < a ^ 2 := by sorry        
    sorry                                     

/- 0.5  Finding the right lemma -/

-- Exercise 0.5.  HINT: put `by exact?` and read Lean's suggestion (it's `sq_nonneg x`).
example (x : ℝ) : 0 ≤ x ^ 2 := by sorry

/- 0.6  Giving hints to tactics -/

-- Exercise 0.6a.  HINT: `linarith [sq_nonneg b]`.
example (a b : ℝ) : a * a ≤ a * a + b ^ 2 := by sorry

-- Exercise 0.6b.  HINT: `simp [h]`.
example (a b : ℕ) (h : a = 0) : a + b = b := by sorry

/- 0.7  The "divides" relation:  a ∣ b  means  ∃ c, b = a * c -/

-- MODEL (worked for you):
example (a b : ℕ) : (a ∣ b) ↔ ∃ c, b = a * c := Iff.rfl

-- Exercise 0.7a.  HINT: give the witness — `⟨3, rfl⟩` (since 6 = 2 * 3).
example : (2 : ℕ) ∣ 6 := by sorry

-- Exercise 0.7b.  HINT: `⟨4, by norm_num⟩`.
example : (3 : ℕ) ∣ 12 := by sorry

/- 0.8  Opening the black box: "a² even ⟹ a even" -/

-- Exercise 0.8.  Strategy: an odd number has an odd square.
theorem even_of_even_sq {a : ℕ} (h : 2 ∣ a ^ 2) : 2 ∣ a := by
  rcases Nat.even_or_odd a with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- a = k + k is even.   HINT: `exact ⟨k, by rw [hk]; ring⟩`.
    sorry
  · -- a = 2*k + 1 is odd ⟹ a² is odd ⟹ contradiction.
    exfalso
    obtain ⟨j, hj⟩ := h                       -- hj : a ^ 2 = 2 * j
    rw [hk] at hj                             -- hj : (2*k+1)^2 = 2*j
    have expand : (2 * k + 1) ^ 2 = 2 * (2 * k ^ 2 + 2 * k) + 1 := by sorry  
    rw [expand] at hj                         -- hj says (odd) = (even)
    sorry                                     

/- 0.9  Strong induction, gently -/

-- MODEL (worked for you): the bare principle. `ih : ∀ m, m < n → R m`.
example (R : ℕ → Prop) (step : ∀ n, (∀ m, m < n → R m) → R n) : ∀ n, R n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih => exact step n ih

-- Exercise 0.9.  Watch `ih` get applied to the smaller value `m`.
example : ∀ n : ℕ, n < 2 ^ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | m
    · sorry                                   
    · have hm   : m < 2 ^ m := by sorry         
      have hpos : 0 < 2 ^ m := by sorry         
      have hpow : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by sorry  
      sorry                                     

/- ========================================================================
   PART 1 — CAUCHY–SCHWARZ
   Find the square; `nlinarith` does the rest.
   ======================================================================== -/

-- MODEL (worked for you):
example (a b : ℝ) (h : a ≤ b) : a - 1 ≤ b := by linarith

-- Exercise 1.1.  HINT: `sq_nonneg x`  (or the `positivity` tactic).
example (x : ℝ) : 0 ≤ x ^ 2 := by sorry

-- Exercise 1.2 — AM–GM.  `linarith` will NOT work (nonlinear).

theorem two_var_amgm (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  sorry

-- Exercise 1.3 — FINALE: Cauchy–Schwarz in 2D.

theorem cauchy_schwarz_2d (a b c d : ℝ) :
    (a * c + b * d) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
  sorry

-- Exercise 1.4 (CHALLENGE) — 3D. THREE cross-terms (the three 2×2 minors).

theorem cauchy_schwarz_3d (a₁ a₂ a₃ b₁ b₂ b₃ : ℝ) :
    (a₁ * b₁ + a₂ * b₂ + a₃ * b₃) ^ 2
      ≤ (a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2) * (b₁ ^ 2 + b₂ ^ 2 + b₃ ^ 2) := by
  sorry

/- ========================================================================
   PART 2 — IRRATIONALITY OF √2 (infinite descent)
   √2 = a/b ⟹ a² = 2b². We show the ONLY natural solution has b = 0.
   (Reuses `even_of_even_sq` from Exercise 0.8.)
   ======================================================================== -/

-- Exercise 2 — FINALE: the descent.
--  ⚠ If `Nat.strong_induction_on` is unknown in your Mathlib, use:
--        induction a using Nat.strongRecOn with
--        | ind a ih =>
theorem no_rational_sqrt_two : ∀ a b : ℕ, a ^ 2 = 2 * b ^ 2 → b = 0 := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro b hab
    rcases Nat.eq_zero_or_pos a with rfl | hapos
    · -- BASE: a = 0.  hab : 0 ^ 2 = 2 * b ^ 2,  goal : b = 0.
      have h0 : 2 * b ^ 2 = 0 := by sorry        
      rcases Nat.eq_zero_or_pos b with rfl | hb
      · sorry                                     
      · exfalso
        have hpos : 0 < b ^ 2 := by sorry         
        sorry                                     
    · -- STEP: a > 0   (hapos : 0 < a)
      have h2a : 2 ∣ a := by sorry                
      obtain ⟨c, rfl⟩ := h2a                      -- a = 2 * c
      have hbc : b ^ 2 = 2 * c ^ 2 := by
        have e : 4 * c ^ 2 = 2 * b ^ 2 := by sorry  
        sorry                                       
      have h2b : 2 ∣ b := by sorry                
      obtain ⟨d, rfl⟩ := h2b                      -- b = 2 * d
      have hcd : c ^ 2 = 2 * d ^ 2 := by
        have e : 4 * d ^ 2 = 2 * c ^ 2 := by sorry  
        sorry                                       
      have hclt : c < 2 * c := by sorry           
      have hd : d = 0 := by sorry                 
      sorry                                        

-- Exercise 2.3 — the library already has the real statement.

example : Irrational (Real.sqrt 2) := by sorry

end Tutorial
