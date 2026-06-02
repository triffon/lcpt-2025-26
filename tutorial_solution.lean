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

#check rfl

/- 0.1  `rfl` and gentle arithmetic -/

-- MODEL (worked for you): `rfl` proves goals true by computation.
example : 2 + 2 = 4 := rfl

-- Exercise 0.1a.  HINT: `rfl` — `n + 0` reduces to `n` by definition.
example (n : ℕ) : n + 0 = n := rfl
theorem t (n : ℕ) : 0 + n = n := Nat.zero_add n

-- (FYI: `0 + n = n` is NOT `rfl`; it needs `Nat.zero_add n`. Try `rfl` to see it fail.)

-- Exercise 0.1b.  HINT: `norm_num`.
example : 17 * 23 = 391 := by norm_num

/- 0.2  `rw` (rewrite with an equation) -/

-- Exercise 0.2a.  HINT: `rw [h]`.
example (a b : ℕ) (h : a = b) : a + 1 = b + 1 := by rw [h]

-- Exercise 0.2b.  HINT: `rw [← h]` (rewrite right→left).
example (a b : ℕ) (h : a = b) : b + 1 = a + 1 := by rw [← h]

/- 0.3  `have` (prove a fact, then reuse it) -/

-- Exercise 0.3.  HINT: `have hsq : 0 ≤ x ^ 2 := sq_nonneg x`, then `linarith`.
example (x : ℝ) : 0 ≤ x ^ 2 + 1 := by
  have hsq : 0 ≤ x ^ 2 := sq_nonneg x
  linarith

example (h : P ∧ Q) : P := by
  rcases h with ⟨ hp, hq ⟩
  exact hp

example (h : P ∨ Q) : Q ∨ P := by
  rcases h with hp | hq
  . exact Or.inr hp
  . exact Or.inl hq

example (a : ℕ) (h : a ^ 2 = 0) : a = 0 := by
  rcases Nat.eq_zero_or_pos a with rfl | hanz
  . rfl
  . exfalso
    have hpos2 : 0 < a ^ 2 := pow_pos hanz 2
    linarith

example (x : ℝ) : 0 ≤ x ^ 2 := sq_nonneg x

example (a b : ℝ) : a * a ≤ a * a + b ^ 2 := by linarith [sq_nonneg b]

#print (fun (a b : ℕ) => (a ∣ b))
example (a b : ℕ) : (a ∣ b) ↔ ∃ c, b = a * c := Iff.rfl

example : (2 : ℕ) ∣ 6 := ⟨3, rfl⟩

#print Odd
#print Even

theorem even_of_even_sq {a : ℕ} (h : 2 ∣ a ^ 2) : 2 ∣ a := by
  rcases Nat.even_or_odd a with ⟨k, hk⟩ | ⟨k, hk⟩
  . exact ⟨k, by rw [hk]; ring⟩
  . exfalso
    -- rcases h with ⟨j, hj⟩
    obtain ⟨j, hj⟩ := h
    rw [hk] at hj
    have expand : (2*k + 1)^2 = 4*k^2 + 4*k + 1 := by ring
    rw [expand] at hj
    omega

theorem two_var_amgm (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by linarith [sq_nonneg (a - b)]

theorem cauchy_schwarz_2d (a b c d : ℝ) :
    (a * c + b * d) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by linarith [sq_nonneg (a*d - b*c)]

example : ∀ n : ℕ, n < 2 ^ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | m
    . norm_num
    . have hm : m < 2 ^ m := ih m (by linarith)
      have hpos : 0 < 2 ^ m := pow_pos (by linarith) m
      have hpowsuc : 2^(m+1) = 2^m + 2^m := by ring
      linarith

theorem no_rational_sqrt_two : ∀ a b : ℕ, a ^ 2 = 2 * b ^ 2 → b = 0 := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro b hab
    rcases Nat.eq_zero_or_pos a with rfl | hapos
    . have h0 : 2 * b^2 = 0 := by rw [← hab]; ring
      rcases Nat.eq_zero_or_pos b with rfl | hbpos
      . rfl
      . exfalso
        have hb2pos : 0 < b^2 := pow_pos hbpos 2
        linarith
    . have h2a : 2 ∣ a := even_of_even_sq ⟨b^2, hab⟩
      obtain ⟨c, rfl⟩ := h2a
      have hbc : b^2 = 2 * c^2 := by
        have e  : 4 * c^2 = 2 * b^2 := by rw [← hab]; ring
        linarith
      have h2b : 2 ∣ b := even_of_even_sq ⟨c^2, hbc⟩
      obtain ⟨d, rfl⟩ := h2b
      have hcd : c^2 = 2 * d^2 := by
        have e  : 4 * d^2 = 2 * c^2 := by rw [← hbc]; ring
        linarith
      have hlt2c : c < 2 * c := by linarith
      have hd : d = 0 := ih c hlt2c d hcd
      linarith
