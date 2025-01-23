import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Duper
import Mathlib.Tactic
import Mathlib.SetTheory.Cardinal.Basic
open Cardinal

macro_rules | `(conv | ring) => `(conv | ring_nf)
macro "ring" : tactic => `(tactic | first | (ring_nf; done) | ring1)

open Set

universe u

def α := Type u

theorem Set.mt_ext_iff {α : Type u} {s t : Set α} : s ≠ t ↔ ¬(∀ (x : α), x ∈ s ↔ x ∈ t) := by
  rw [not_iff_not, Set.ext_iff]

macro_rules | `(tactic | ext) => `(tactic | rw [Set.mt_ext_iff])

attribute [default_instance] Set.instSingletonSet
attribute [default_instance] Set.instEmptyCollection

@[simp] theorem Set.mem_insert_eq {x a : α} {s : Set α} : (x ∈ insert a s) = (x = a ∨ x ∈ s) := rfl
@[simp] theorem Set.mem_singleton_eq {x y : α} : (x ∈ ({y} : Set α)) = (x = y) := rfl

@[simp] theorem Set.mem_union_eq (x : α) (a b : Set α) : (x ∈ a ∪ b) = (x ∈ a ∨ x ∈ b) := rfl
@[simp] theorem Set.mem_inter_eq (x : α) (a b : Set α) : (x ∈ a ∩ b) = (x ∈ a ∧ x ∈ b) := rfl
@[simp] theorem Set.mem_compl_eq (s : Set α) (x : α) : (x ∈ sᶜ) = ¬x ∈ s := rfl

@[simp] theorem Set.mem_empty_eq_false (x : α) : (x ∈ ∅) = False := rfl
@[simp] theorem Set.mem_univ_eq (x : α) : (x ∈ univ) = True := rfl

section
  variable (A : Set α)
  variable (a : α)
  variable (b : α)
  variable (B : Set α)

  -- Set membership
  #check a ∈ A
  #check a ∉ A

  -- Logical Identity
  #check a = b
  #check A = B
  #check a ≠ b
  #check A ≠ B

  -- Example set disequality
  example : {a : ℝ | 0 ≤ a} ≠ {b : ℝ | 0 < b} := by
    ext
    push_neg
    use 0
    constructor
    · constructor
      · dsimp
        norm_num
      dsimp
      norm_num

  -- Subsets
  -- proper inclusion
  notation:50 a:50 " ⊊ " b:50 => a ⊆ b ∧ a ≠ b
  notation:50 a:50 " ⊈ " b:50 => ¬ (a ⊆ b)

  #check A ⊊ B
  #check {1, 2, 3}
  #check {x : ℤ | Even x}
  #check A ∪ B
  #check A ∩ B
  #check ∅

  example : a ∉ ∅ := by 
    duper
end


-- hypotheses
example (x : ℝ) (hx : 0 < x) : x ^ 3 ≠ 0 := by 
  have := calc
    x ^ 3 = x * x ^ 2 := by ring
    _ > 0 * x ^ 2 := by gcongr
    _ = 0 := by ring
  apply ne_of_gt
  apply this

-- a "vacuously true" statement
example (x : ℝ) (hx : x ^ 2 < 0) : x = 23 := by
  have : 0 ≤ x ^ 2 := by positivity
  apply not_lt_of_le at this
  tauto

-- another "vacuously true" statement
example (A : Set α) : ∅ ⊆ A := by 
  dsimp [Set.subset_def]
  intro x hx
  tauto

-- contrapositive
example (x : ℝ) : 0 < x → 0 < x ^ 2  := by
  contrapose
  intro hx
  apply le_of_not_lt at hx
  intro hx2
  have hx1 : 0 ≤ x ^ 2 := by positivity
  have hx3 : x ^ 2 = 0 := by 
    apply le_antisymm
    apply hx
    apply hx1
  have : x = 0 := by exact pow_eq_zero hx3 
  apply ne_of_lt at hx2
  symm at hx2
  tauto

section
  variable (P : Prop)
  variable (Q : Prop)

  #check P → Q
  #check ¬Q → ¬P
end

example (p q : Prop) : p → q ↔ ¬q → ¬p := by 
  constructor
  · intro h nq np
    apply h at np
    tauto
  intro h p2
  contrapose h
  push_neg
  constructor
  · exact h
  exact p2

-- Quantifiers
section
def P (x : α) : Prop := sorry

#check P

def B (X : Set α) := {b ∈ X | P b} 

example (A X : Set α) (hA : A ⊆ X) (hAx : ∀ x ∈ A, P x) : A ⊆ B X := by
  dsimp [Set.subset_def] at *
  intro x hx
  rw [B]
  dsimp
  constructor
  apply hA
  apply hx
  apply hAx
  apply hx

-- Negation
example (A X : Set α) (hA : A ⊆ X) : A ⊈ B X → ∃ x : α, x ∈ A ∧ ¬ (P x) := by 
  intro h
  dsimp [Set.subset_def] at *
  push_neg at h
  rw [B] at h
  obtain ⟨x, ⟨hxA, hxB⟩⟩ := h
  dsimp at *
  push_neg at *
  use x
  constructor
  · apply hxA
  apply hxB
  apply hA
  apply hxA

end

-- Difference of Sets
-- in Mathlib, `\` is the set difference operator 


example (A B : Set α): A \ B = {x | x ∈ A ∧ x ∉ B} := by 
  ext x
  constructor
  · intro hx
    rw [Set.diff_eq] at hx
    rw [Set.compl_def] at hx
    obtain ⟨h1, h2⟩ := hx
    dsimp at *
    constructor
    · apply h1
    apply h2
  intro hx
  rw [Set.diff_eq, Set.compl_def]
  obtain ⟨h1, h2⟩ := hx
  dsimp
  constructor
  · apply h1
  apply h2

-- a.k.a `inter_union_distrib_left`
example (A B C : Set α) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x
  constructor
  · intro ⟨hxA, h2⟩
    dsimp at *
    obtain hxB | hxC := h2
    · left
      constructor
      · apply hxA
      apply hxB
    · right
      constructor
      · apply hxA
      apply hxC
  intro H
  dsimp at *
  obtain ⟨hxA, hxB⟩ | ⟨hxA, hxC⟩ := H
  · constructor
    · apply hxA
    left
    apply hxB
  constructor
  · apply hxA
  right
  apply hxC

-- a.k.a. `union_inter_distrib_left`
example (A B C : Set α) : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  ext x
  constructor
  · intro H
    dsimp at *
    obtain hxA | ⟨hxB, hxC⟩ := H
    · constructor
      · left
        apply hxA
      left
      apply hxA
    constructor
    · right
      apply hxB
    right
    apply hxC
  intro H
  dsimp at *
  obtain ⟨hxA | hxB, hxA | hxC⟩ := H
  · left
    apply hxA
  · left
    apply hxA
  · left
    apply hxA
  · right
    constructor
    · apply hxB
    apply hxC

-- DeMorgan's laws for sets
-- a.k.a. diff_inter_diff (the name comes from the latter half of the statement)
example (A B C : Set α) : A \ (B ∪ C) = (A \ B) ∩ (A \ C) := by 
  repeat rw [Set.diff_eq, Set.compl_def]
  ext x
  constructor
  · intro H
    dsimp at *
    push_neg at *
    obtain ⟨hxA, hxnB, hxnC⟩ := H
    constructor
    · constructor
      · apply hxA
      apply hxnB
    constructor
    · apply hxA
    apply hxnC
  intro H
  dsimp at *
  obtain ⟨⟨hxA, hxnB⟩, hxA, hxnC⟩ := H
  push_neg
  constructor
  · apply hxA
  constructor
  · apply hxnB
  apply hxnC

-- a.k.a. diff_inter
example (A B C : Set α) : A \ (B ∩ C) = (A \ B) ∪ (A \ C) := by
  repeat rw [Set.diff_eq, Set.compl_def]
  ext x
  constructor
  · intro H
    dsimp at *
    push_neg at *
    obtain ⟨hxA, h2⟩ := H
    by_cases h : x ∈ B
    · right
      constructor
      · apply hxA
      apply h2
      apply h
    left
    constructor
    · apply hxA
    apply h
  intro H
  dsimp at *
  push_neg at *
  obtain ⟨hxA, hnxB⟩ | ⟨hxA, hnxC⟩ := H
  · constructor
    · apply hxA
    intro hxB
    tauto
  constructor
  · apply hxA
  intro hxB
  apply hnxC

-- The powerset is the set of all subsets of a set
section
  variable (A : Set α)
  #check 𝒫 A
end

-- Sets of sets usually are denoted with script letters
section
  variable (𝒜 : Set (Set α))

  -- Arbitrary Unions
  #check ⋃₀ 𝒜 
  #check ⋃ A ∈ 𝒜, A
end

-- Indexed Unions
example (𝒜 : Set (Set α)) : ⋃ A ∈ 𝒜, A = {x : α | ∃ A ∈ 𝒜, x ∈ A} := by
  ext x
  constructor
  · intro H
    simp only [mem_iUnion] at H
    obtain ⟨I, ⟨hI, hxI⟩⟩ := H
    dsimp
    use I
  intro H
  simp only [mem_iUnion] at H
  obtain ⟨A, ⟨hAA, hxA⟩⟩ := H
  simp only [mem_iUnion]
  use A

-- Indexed Intersections
example (𝒜: Set (Set α)) : ⋂ A ∈ 𝒜, A = {x : α | ∀ A ∈ 𝒜, x ∈ A} := by 
  ext x
  constructor
  · intro H
    simp only [mem_iInter] at H
    dsimp
    apply H
  · intro H
    simp only [mem_iInter]
    intro I hI
    dsimp at *
    apply H at hI
    apply hI

-- Cartesian Products of Sets
-- In Lean, the `×ˢ` symbol indicates a Cartesian product
section
  variable (A B : Set α)
  #check A ×ˢ B
  #check {(a, b) : α × α | a ∈ A ∧ b ∈ B}
end

example (A B : Set α) : A ×ˢ B = {(a, b) : α × α | a ∈ A ∧ b ∈ B} := by 
  ext ⟨x1, x2⟩ 
  constructor
  · intro H
    simp at H
    obtain ⟨hxA, hxB⟩ := H
    constructor
    · apply hxA
    apply hxB
  · intro H
    dsimp at H
    obtain ⟨hxA, hxB⟩ := H
    constructor
    · apply hxA
    apply hxB


-- Exercises
section
  -- Skipping 1 since that is already completed above
  -- 2. Determine which statements are true below.  If a statement is not true, reframe it so that it is by replacing the `=` symbol with the appropriate symbol.  If an `↔` statement is not true, determine which direction is true.
  -- 2.a
  -- only forward direction can be proved since ∃ A : Set α, A ⊆ (B ∩ C)
  example (A B C : Set α) : A ⊆ B ∧ A ⊆ C → A ⊆ (B ∪ C) := by 
    intro ⟨hA, hB⟩ 
    dsimp [Set.subset_def] at *
    intro x hx
    left
    apply hA
    apply hx

  -- 2.b
  -- only forward direction can be proved since ∃ A : Set α, A ⊆ (B ∩ C)
  example (A B C : Set α) : A ⊆ B ∨ A ⊆ C → A ⊆ (B ∪ C) := by
    intro H
    obtain hAB | hAC := H
    · dsimp [Set.subset_def] at *
      intro x hxA
      left
      apply hAB
      apply hxA
    · dsimp [Set.subset_def] at *
      intro x hxA
      right
      apply hAC
      apply hxA

  -- 2.c
  example (A B C : Set α) : A ⊆ B ∧ A ⊆ C ↔ A ⊆ (B ∩ C) := by 
    constructor
    · intro ⟨hAB, hAC⟩ 
      dsimp [Set.subset_def] at *
      intro x hxA
      constructor
      · apply hAB
        apply hxA
      apply hAC
      apply hxA
    · intro H
      dsimp [Set.subset_def] at *
      constructor
      · intro x hxA
        apply H at hxA
        obtain ⟨hxB, hxC⟩ := hxA
        apply hxB
      intro x hxA
      apply H at hxA
      obtain ⟨hxB, hxC⟩ := hxA
      apply hxC

  -- 2.d
  -- only the backward direction can be proved since ∃ A, A ⊆ B ∧ A ⊈ C
  example (A B C : Set α) : A ⊆ (B ∩ C) → A ⊆ B ∨ A ⊆ C := by
    intro H
    dsimp [Set.subset_def] at *
    left
    intro x hxA
    apply H at hxA
    obtain ⟨hxB, hxC⟩ := hxA
    apply hxB

  -- 2.e
  example (A B : Set α) : A \ (A \ B) = A \ B := by
    sorry

  -- this becomes equivalent to A ∩ B, not A \ B
  -- not sure how to prove A ∩ B ≠ A \ B yet,
  -- but it leads to a contradiction around membership of B
  example (A B : Set α) : A \ (A \ B) = A ∩ B := by
    ext x
    constructor
    · intro hx
      repeat rw [Set.diff_eq, Set.compl_def] at hx
      dsimp at *
      push_neg at *
      obtain ⟨hxA, hxAB⟩ := hx
      constructor
      · apply hxA
      apply hxAB
      apply hxA
    intro hxAB
    repeat rw [Set.diff_eq, Set.compl_def]
    dsimp at *
    push_neg at *
    obtain ⟨hxA, hxB⟩ := hxAB
    constructor
    · apply hxA
    intro hxA2
    apply hxB

  -- 2.f
  example (A B : Set α) : A \ (B \ A) = A \ B := by
    sorry

  -- This becomes equivalent to A, not A \ B
  -- A = A \ B ↔ A ∩ B = ∅
  example (A B : Set α) : A \ (B \ A) = A := by 
    ext x
    repeat rw [Set.diff_eq, Set.compl_def]
    constructor
    · intro H
      dsimp at H
      push_neg at H
      obtain ⟨hxA, hxBA⟩ := H
      apply hxA
    · intro hxA
      dsimp
      push_neg
      constructor
      · apply hxA
      intro hxB
      apply hxA

  -- 2.g
  example (A B C : Set α) : A ∩ (B \ C) = (A ∩ B) \ (A ∩ C) := by 
    ext x
    repeat rw [Set.diff_eq, Set.compl_def]
    constructor
    · intro H
      dsimp at *
      obtain ⟨hxA, hxB, hxnC⟩ := H
      push_neg
      constructor
      · constructor
        · apply hxA
        apply hxB
      intro hxA
      apply hxnC
    · intro H
      dsimp at *
      push_neg at *
      obtain ⟨⟨hxA, hxB⟩, hxAnC⟩ := H
      constructor
      · apply hxA
      constructor
      · apply hxB
      apply hxAnC
      apply hxA

  -- 2.h
  example (A B C : Set α) : (A ∪ B) \ (A ∪ C) ⊆ A ∪ (B \ C)   := by
    intro x H
    repeat rw [Set.diff_eq, Set.compl_def] at *
    dsimp at *
    push_neg at *
    obtain ⟨hxA | hxB, ⟨hxnA, hxnC⟩⟩ := H
    · left
      apply hxA
    right
    constructor
    · apply hxB
    apply hxnC

  -- 2.i
  example (A B : Set α) : (A ∩ B) ∪ (A \ B) = A := by
    ext x
    repeat rw [Set.diff_eq, Set.compl_def]
    dsimp
    constructor
    · intro H
      obtain ⟨hxA, hxB⟩ | ⟨hxA, hxnB⟩ := H
      · apply hxA
      apply hxA
    intro hxA
    by_cases hxB : x ∈ B
    · left
      constructor
      · apply hxA
      apply hxB
    · right
      constructor
      · apply hxA
      apply hxB

  -- 2.j
  example (A B C D : Set α) : A ⊆ C ∧ B ⊆ D → (A ×ˢ B) ⊆ (C ×ˢ D) := by
    simp
    intro hAC hBD
    dsimp [Set.subset_def] at *
    intro (x1, x2) hx
    obtain ⟨hx1A, hx2B⟩ := hx
    dsimp at *
    apply hAC at hx1A
    apply hBD at hx2B
    simp
    constructor
    · apply hx1A
    apply hx2B

  -- 2.k
  -- This example is false
  example (A B C D : Set α) : A ⊆ C ∧ B ⊆ D → (A ×ˢ B) ⊈ (C ×ˢ D) := by
    sorry

  -- 2.l
  -- This example is still false
  example (A B C D : Set α) (hA : A ≠ ∅) (hB : B ≠ ∅) : A ⊆ C ∧ B ⊆ D → (A ×ˢ B) ⊈ (C ×ˢ D) := by
    intro ⟨hAC, hBD⟩
    rw [Set.subset_def] at *
    push_neg at *
    rw [nonempty_def] at hB
    rw [nonempty_def] at hA
    obtain ⟨a, hA⟩ := hA
    obtain ⟨b, hB⟩ := hB
    use (a, b)
    simp
    constructor
    · constructor
      · apply hA
      apply hB
    intro haC
    apply hBD at hB
    -- no way to prove b ∉ D here
    sorry

  -- 2.m
  -- Changed to `⊆` since you can have pairs from C ∪ B 
  -- in (A ∪ C) ×ˢ (B ∪ D) that aren't in the left side
  example (A B C D : Set α) : (A ×ˢ B) ∪ (C ×ˢ D) ⊆ (A ∪ C) ×ˢ (B ∪ D) := by
    rw [Set.subset_def]
    intro ⟨x1, x2⟩ H
    simp at *
    obtain ⟨hx1A, hx2B⟩ | ⟨hx1C, hx2D⟩ := H
    · left
      left
      constructor
      · apply hx1A
      apply hx2B
    right
    right
    constructor
    · apply hx1C
    apply hx2D

  -- 2.n
  example (A B C D : Set α) : (A ×ˢ B) ∩ (C ×ˢ D) = (A ∩ C) ×ˢ (B ∩ D) := by
    ext x
    obtain ⟨x1, x2⟩ := x
    constructor
    · intro H
      simp at *
      obtain ⟨⟨hx1A, hx2B⟩, ⟨hx1C, hx2D⟩⟩ := H 
      constructor
      · constructor
        · apply hx1A
        apply hx1C
      constructor
      · apply hx2B
      apply hx2D
    intro H
    simp at *
    obtain ⟨⟨hx1A, hx1C⟩, ⟨hx2B, hx2D⟩⟩ := H
    constructor
    · constructor
      · apply hx1A
      apply hx2B
    constructor
    · apply hx1C
    apply hx2D

  -- 2.o
  example (A B C : Set α) : A ×ˢ (B \ C) = A ×ˢ B \ A ×ˢ C := by
    ext x
    obtain ⟨x1, x2⟩ := x
    simp
    constructor
    · intro ⟨hx1A, ⟨hx2B, hx2nC⟩⟩
      constructor
      · constructor
        · apply hx1A
        apply hx2B
      intro hx1A
      apply hx2nC
    intro ⟨⟨hx1A, hx2B⟩, hx1AC⟩ 
    constructor
    · apply hx1A
    constructor
    · apply hx2B
    apply hx1AC
    apply hx1A

  -- 2.p
  -- Changed to `⊆` because you can have elements from `A ×ˢ C` in the right and not left
  example (A B C D : Set α) : (A \ B) ×ˢ (C \ D) ⊆ (A ×ˢ C \ B ×ˢ C) \ (A ×ˢ D) := by 
    repeat rw [Set.diff_eq, Set.compl_def, Set.subset_def]
    intro ⟨x1, x2⟩ H
    simp at *
    obtain ⟨⟨hx1A, hx1nB⟩, ⟨hx2C, hx2nD⟩⟩ := H
    · constructor
      · constructor
        · constructor
          · apply hx1A
          apply hx2C
        intro hx1B
        tauto
      intro hx1A
      apply hx2nD

  -- 2.q
  -- Changed to `⊇` 
  example (A B C D : Set α) : (A \ C) ×ˢ (B \ D) ⊆ (A ×ˢ B) \ (C ×ˢ D)  := by
    rw [Set.subset_def]
    simp
    intro x1 x2 hx1A hx1nC hx2B hx2nD
    constructor
    · constructor
      · apply hx1A
      apply hx2B
    intro hx1C
    apply hx2nD

  -- 3: Write the contrapositive and converse of the following statement, and determine which of the three statements is true.
  -- 3.a "If x < 0, then x² - x > 0"
  -- 3.a.1 original statement
  example (x : ℝ) (hx : x < 0) : 0 < x ^ 2 - x := by 
    have hx2 : 0 ≤ x ^ 2 := by positivity
    have hx3 : 0 < -x := by exact Left.neg_pos_iff.mpr hx 
    calc
      0 = 0 + 0 := by ring
      _ ≤ x ^ 2 + 0 := by gcongr
      _ < x ^ 2 + -x := by gcongr
      _ = x ^ 2 - x := by ring

  -- 3.a.2 contrapositive statement
  example (x : ℝ) (hx : x ^ 2 - x ≤ 0) : 0 ≤ x := by
    have hx2x : x ^ 2 ≤ x := by exact tsub_nonpos.mp hx 
    have h1 : 0 ≤ x ^ 2 := by positivity
    calc
      0 ≤ x ^ 2 := h1
      _ ≤ x := by gcongr

  -- 3.a.3 converse statement
  -- False by 3.a.1
  example (x : ℝ) (hx : x < 0) : x ^ 2 - x ≤ 0 := by
    sorry

  -- 3.b "If x > 0, then x² - x > 0"
  -- None of the statements are true since the statement is only 
  -- true when 0 < x < 1

  -- 3.b.1 original statement
  example (x : ℝ) (hx : x > 0) : 0 < x ^ 2 - x := by
    sorry

  -- 3.b.2 contrapositive statement
  example (x : ℝ) (hx : x ^ 2 - x ≤ 0) : x > 0 := by
    sorry

  -- 3.b.3 converse statement
  example (x : ℝ) (hx : x > 0) : x ^ 2 - x ≤ 0 := by
    sorry

  -- 4. Write the negation of the following statements
  -- 4.a
  example (A B : Set ℝ) : (¬(∀ a ∈ A, a ^ 2 ∈ B)) = ∃ a ∈ A, a ^ 2 ∉ B := by
    push_neg
    rfl

  -- 4.b
  example (A B : Set ℝ) : (¬(∃ a ∈ A, a ^ 2 ∈ B)) = ∀ a ∈ A, a ^ 2 ∉ B := by
    push_neg
    rfl

  -- 4.c
  example (A B : Set ℝ) : (¬(∀ a ∈ A, a ^ 2 ∉ B)) = ∃ a ∈ A, a ^ 2 ∈ B := by
    push_neg
    rfl

  -- 4.d
  example (A B : Set ℝ) : (¬(∃ a ∉ A, a ^ 2 ∈ B)) = ∀ a ∉ A, a ^ 2 ∉ B := by
    push_neg
    rfl

  -- 5. Determine which of the following and their converses are true
  -- 5.a
  example (𝒜 : Set (Set α)) (x : α) (h𝒜 : 𝒜 ≠ ∅) : x ∈ ⋃ A ∈ 𝒜, A → ∃ A ∈ 𝒜, x ∈ A := by
    intro H
    simp at H
    obtain ⟨I, ⟨hIA, hxI⟩⟩ := H
    use I

  -- 5.b
  -- neither the statement nor its converse are true
  -- `x` can be a member of only one set `A ∈ 𝒜` from 5.a

  example (𝒜 : Set (Set α)) (x : α) (h𝒜 : 𝒜 ≠ ∅) : x ∈ ⋃ A ∈ 𝒜, A → ∀ A ∈ 𝒜, x ∈ A := by
    sorry

  example (𝒜 : Set (Set α)) (x : α) (h𝒜 : 𝒜 ≠ ∅) : x ∈ ⋃ A ∈ 𝒜, A → ¬(∀ A ∈ 𝒜, x ∈ A) := by
    sorry

  -- 5.c
  example (𝒜 : Set (Set α)) (x : α) (h𝒜 : 𝒜 ≠ ∅) : x ∈ ⋂ A ∈ 𝒜, A → ∃ A ∈ 𝒜, x ∈ A := by
    intro H
    simp at H
    rw [← nonempty_iff_ne_empty, Set.nonempty_def] at h𝒜 
    obtain ⟨A, hxA⟩ := h𝒜
    use A
    constructor
    · apply hxA
    apply H
    apply hxA

  -- 5.d
  example (𝒜 : Set (Set α)) (x : α) (h𝒜 : 𝒜 ≠ ∅) : x ∈ ⋂ A ∈ 𝒜, A → ∀ A ∈ 𝒜, x ∈ A := by
    intro H A hA𝒜 
    simp at H
    apply H
    apply hA𝒜 

  -- 6. Write the contrapositive for each of the statements in problem 5
  -- 6.a
  example (𝒜 : Set (Set α)) (x : α) (h𝒜 : 𝒜 ≠ ∅) : (¬ ∃ A ∈ 𝒜, x ∈ A) → ¬ x ∈ ⋃ A ∈ 𝒜, A := by
    sorry

  -- 6.b
  example (𝒜 : Set (Set α)) (x : α) (h𝒜 : 𝒜 ≠ ∅) : (¬ ∀ A ∈ 𝒜, x ∈ A) → ¬ x ∈ ⋃ A ∈ 𝒜, A := by
    sorry

  -- 6.c
  example (𝒜 : Set (Set α)) (x : α) (h𝒜 : 𝒜 ≠ ∅) : (¬ ∃ A ∈ 𝒜, x ∈ A) → ¬ x ∈ ⋂ A ∈ 𝒜, A := by 
    sorry

  -- 6.d
  example (𝒜 : Set (Set α)) (x : α) (h𝒜 : 𝒜 ≠ ∅) : (¬ ∀ A ∈ 𝒜, x ∈ A) → ¬ x ∈ ⋂ A ∈ 𝒜, A := by 
    sorry

  -- 7. Use `∪`, `∩`, or `\` to fill in the equivalent expression denoted with `sorry`
  -- 7.a 
  example (A B C : Set α) : {x : α | x ∈ A ∧ (x ∈ B ∨ x ∈ C)} = A ∩ (B ∪ C) := by 
    rfl

  -- 7.b
  example (A B C : Set α) : {x : α | (x ∈ A ∧ x ∈ B) ∨ x ∈ C} = (A ∩ B) ∪ C := by
    rfl

  -- 7.c
  example (A B C : Set α) : {x : α | x ∈ A ∧ (x ∈ B → x ∈ C)} = A \ (B \ C) := by
    ext x
    simp

  -- 8
  -- Cardinality is represented by the `#` symbol
  example (A : Set α) (hA : #A = 2) : toNat #(𝒫 A) = 4 := by
    rw [mk_powerset, hA]
    norm_cast

  example (A : Set α) (hA : #A = 1) : toNat #(𝒫 A) = 2 := by
    rw [mk_powerset, hA]
    norm_cast

  -- 9.a
  example (A : Set α) (ℬ : Set (Set α)) (hℬ : ℬ ≠ ∅) : A \ (⋃ B ∈ ℬ, B) = ⋂ B ∈ ℬ, A \ B := by
    ext x
    simp
    constructor
    · intro ⟨hxA, H⟩ I hIB
      constructor
      · apply hxA
      apply H
      apply hIB
    · intro H
      rw [← nonempty_iff_ne_empty, nonempty_def] at hℬ 
      obtain ⟨I, hIB⟩ := hℬ 
      have h : x ∈ A ∧ x ∉ I := by 
        apply H
        apply hIB
      obtain ⟨hxA, hxnI⟩ := h
      constructor
      · apply hxA
      intro J hJℬ
      have h : x ∈ A ∧ x ∉ J := by
        apply H
        apply hJℬ
      obtain ⟨_, hxnJ⟩ := h
      apply hxnJ

  example (A : Set α) (ℬ : Set (Set α)) (hℬ : ℬ ≠ ∅) : A \ ⋂ B ∈ ℬ, B = ⋃ B ∈ ℬ, A \ B := by
    ext x
    simp

  -- Determine which of the following statements are true
  def IsInteger (x : ℝ) : Prop := x = Int.floor x

  -- 10.a
  example : ∃ X Y : Set ℝ, {(x, y) : ℝ × ℝ | IsInteger x} = X ×ˢ Y := by
    use {x | IsInteger x}, {y : ℝ | True}
    ext x
    obtain ⟨x1, x2⟩ := x
    simp

  -- 10.b
  example : ∃ X Y : Set ℝ, {(x, y) : ℝ × ℝ | 0 < y ∧ y ≤ 1} = X ×ˢ Y := by
    use {x : ℝ | True}, {y : ℝ | 0 < y ∧ y ≤ 1}
    ext x
    obtain ⟨x1, x2⟩ := x
    simp

  -- 10.c
  -- This example cannot be completed
  example : ∃ X Y : Set ℝ, {(x, y) : ℝ × ℝ | x < y} = X ×ˢ Y := by 
    sorry

  -- 10.d
  example : ∃ X Y : Set ℝ, {(x, y) : ℝ × ℝ | ¬(IsInteger x) ∧ IsInteger y} = X ×ˢ Y := by
    use {x : ℝ | ¬ IsInteger x}, {y : ℝ | IsInteger y}
    ext x
    obtain ⟨x1, x2⟩ := x
    simp

  -- 10.e
  -- This example cannot be completed
  example : ∃ X Y : Set ℝ, {(x, y) : ℝ × ℝ | x ^ 2 + y ^ 2 < 1} = X ×ˢ Y := by 
    sorry

end
