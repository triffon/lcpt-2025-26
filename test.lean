import Mathlib.Tactic

-- ==========================================
-- 1. ALGORITHM IMPLEMENTATION
-- ==========================================

/-- Inserts an element into a sorted list of natural numbers. -/
def insertSorted (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: bs =>
    if a ≤ b then
      a :: b :: bs
    else
      b :: insertSorted a bs

/-- Sorts a list of natural numbers using insertion sort. -/
def insertionSort : List Nat → List Nat
  | [] => []
  | a :: as => insertSorted a (insertionSort as)

-- ==========================================
-- 2. DEFINING CORRECTNESS (SORTEDNESS)
-- ==========================================

/-- An inductive predicate defining what it means for a list to be sorted. -/
inductive IsSorted : List Nat → Prop where
  | nil : IsSorted []
  | single (a : Nat) : IsSorted [a]
  | cons {a b : Nat} {bs : List Nat} (hab : a ≤ b) (h : IsSorted (b :: bs)) : IsSorted (a :: b :: bs)

-- ==========================================
-- 3. PROVING CORRECTNESS
-- ==========================================

/-- Helper lemma: inserting into a sorted list maintains sortedness. -/
theorem insertSorted_is_sorted (a : Nat) (l : List Nat) (hl : IsSorted l) : IsSorted (insertSorted a l) := by
  induction l with
  