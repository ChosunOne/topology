import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Set
import Mathlib.Data.Set.Basic
import Duper
import Mathlib.Tactic.Ring
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

#check α
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
  example (A B C : Set α) : A ∪ (B \ C) = (A ∪ B) \ (A ∪ C) := by
    sorry

  -- 2.i
  example (A B : Set α) : (A ∩ B) ∪ (A \ B) = A := by
    sorry

  -- 2.j
  example (A B C D : Set α) : A ⊆ C ∧ B ⊆ D → (A ×ˢ B) ⊆ (C ×ˢ D) := by
    sorry

  -- 2.k
  example (A B C D : Set α) : A ⊆ C ∧ B ⊆ D → (A ×ˢ B) ⊈ (C ×ˢ D) := by
    sorry

  -- 2.l
  example (A B C D : Set α) (hA : A ≠ ∅) (hB : B ≠ ∅) : A ⊆ C ∧ B ⊆ D → (A ×ˢ B) ⊈ (C ×ˢ D) := by
    sorry

  -- 2.m
  example (A B C D : Set α) : (A ×ˢ B) ∪ (C ×ˢ D) = (A ∪ C) ×ˢ (B ∪ D) := by
    sorry

  -- 2.n
  example (A B C D : Set α) : (A ×ˢ B) ∩ (C ×ˢ D) = (A ∩ C) ×ˢ (B ∩ D) := by
    sorry

  -- 2.o
  example (A B C : Set α) : A ×ˢ (B \ C) = A ×ˢ B \ A ×ˢ C := by
    sorry

  -- 2.p
  example (A B C D : Set α) : (A \ B) ×ˢ (C \ D) = (A ×ˢ C \ B ×ˢ C) \ (A ×ˢ D) := by 
    sorry

  -- 2.q
  example (A B C D : Set α) : (A ×ˢ B) \ (C ×ˢ D) = (A \ C) ×ˢ (B \ D) := by
    sorry

  -- 3: Write the contrapositive and converse of the following statement, and determine which of the three statements is true.
  -- 3.a "If x < 0, then x² - x > 0"

  -- 3.b "If x > 0, then x² - x > 0"

  -- 4. Write the negation of the following statements
  -- 4.a
  example (A B : Set ℝ) : ¬(∀ a ∈ A, a ^ 2 ∈ B) = sorry := by
    sorry

  -- 4.b
  example (A B : Set ℝ) : ¬(∃ a ∈ A, a ^ 2 ∈ B) = sorry := by
    sorry

  -- 4.c
  example (A B : Set ℝ) : ¬(∀ a ∈ A, a ^ 2 ∉ B) = sorry := by
    sorry

  -- 4.d
  example (A B : Set ℝ) : ¬(∃ a ∉ A, a ^ 2 ∈ B) = sorry := by
    sorry

  -- 5. Determine which of the following and their converses are true
  -- 5.a
  example (𝒜 : Set (Set α)) (x : α) (h𝒜 : 𝒜 ≠ ∅) : x ∈ ⋃ A ∈ 𝒜, A → ∃ A ∈ 𝒜, x ∈ A := by
    sorry

  example (𝒜 : Set (Set α)) (x : α) (h𝒜 : 𝒜 ≠ ∅) : x ∈ ⋃ A ∈ 𝒜, A → ¬(∃ A ∈ 𝒜, x ∈ A) := by
    sorry

  -- 5.b
  example (𝒜 : Set (Set α)) (x : α) (h𝒜 : 𝒜 ≠ ∅) : x ∈ ⋃ A ∈ 𝒜, A → ∀ A ∈ 𝒜, x ∈ A := by
    sorry

  example (𝒜 : Set (Set α)) (x : α) (h𝒜 : 𝒜 ≠ ∅) : x ∈ ⋃ A ∈ 𝒜, A → ¬(∀ A ∈ 𝒜, x ∈ A) := by
    sorry

  -- 5.c
  example (𝒜 : Set (Set α)) (x : α) (h𝒜 : 𝒜 ≠ ∅) : x ∈ ⋂ A ∈ 𝒜, A → ∃ A ∈ 𝒜, x ∈ A := by
    sorry

  example (𝒜 : Set (Set α)) (x : α) (h𝒜 : 𝒜 ≠ ∅) : x ∈ ⋂ A ∈ 𝒜, A → ¬(∃ A ∈ 𝒜, x ∈ A) := by
    sorry

  -- 5.d
  example (𝒜 : Set (Set α)) (x : α) (h𝒜 : 𝒜 ≠ ∅) : x ∈ ⋂ A ∈ 𝒜, A → ∀ A ∈ 𝒜, x ∈ A := by
    sorry

  example (𝒜 : Set (Set α)) (x : α) (h𝒜 : 𝒜 ≠ ∅) : x ∈ ⋂ A ∈ 𝒜, A → ¬(∀ A ∈ 𝒜, x ∈ A) := by
    sorry
  
  -- 6. Write the contrapositive for each of the statements in problem 5
  
  -- 7. Use `∪`, `∩`, or `\` to fill in the equivalent expression denoted with `sorry`
  -- 7.a 
  example (A B C : Set α) : {x : α | x ∈ A ∧ (x ∈ B ∨ x ∈ C)} = sorry := by 
    sorry

  -- 7.b
  example (A B C : Set α) : {x : α | (x ∈ A ∧ x ∈ B) ∨ x ∈ C} = sorry := by
    sorry

  -- 7.c
  example (A B C : Set α) : {x : α | x ∈ A ∧ (x ∈ B → x ∈ C)} = sorry := by
    sorry

  -- 8
  -- Cardinality is represented by the `#` symbol
  example (A : Set α) (hA : #A = 2) : #(𝒫 A) = 4 := by
    sorry

  example (A : Set α) (hA : #A = 1) : #(𝒫 A) = sorry := by
    sorry

  -- 9.a
  example (𝒜 : Set (Set α)) : ¬(⋃ A ∈ 𝒜, A) = sorry := by
    sorry

  example (𝒜 : Set (Set α)) : ¬(⋂ A ∈ 𝒜, A) = sorry := by
    sorry

  -- 10.a
  def IsInteger (x : ℝ) : Prop := sorry

  example : ∃ X Y : Set ℝ, {(x, y) : ℝ × ℝ | IsInteger x} = X ×ˢ Y := by
    sorry

  -- 10.b
  example : ∃ X Y : Set ℝ, {(x, y) : ℝ × ℝ | 0 < y ∧ y ≤ 1} = X ×ˢ Y := by
    sorry

  -- 10.c
  example : ∃ X Y : Set ℝ, {(x, y) : ℝ × ℝ | x < y} = X ×ˢ Y := by 
    sorry

  -- 10.d
  example : ∃ X Y : Set ℝ, {(x, y) : ℝ × ℝ | ¬(IsInteger x) ∧ IsInteger y} = X ×ˢ Y := by
    sorry

  -- 10.e
  example : ∃ X Y : Set ℝ, {(x, y) : ℝ × ℝ | x ^ 2 + y ^ 2 < 1} = X ×ˢ Y := by 
    sorry

end
