import Mathlib
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

open Set

universe u v

-- The subset of `C` such that there exists an element in `D` that the pair `(c, d)` is in `r`
-- In mathlib, this is denoted by `preimage f B` or `f ⁻¹' B`
def Domain {α : Type u} {β : Type v} {C : Set α} {D : Set β} (r : Set (α × β)) {_ : r ⊆ C ×ˢ D} : Set α 
  := {c ∈ C | ∃ d ∈ D, (c, d) ∈ r}

-- The subset of `D` such that there exists an element in `C` that the pair `(c, d)` is in `r`
-- In mathlib, this is denoted by `image f B` or `f '' B`
def Image {α : Type u} {β : Type v} {C : Set α} {D : Set β} (r : Set (α × β)) {_ : r ⊆ C ×ˢ D} : Set β 
  := {d ∈ D | ∃ c ∈ C, (c, d) ∈ r}

-- A "rule of assignment" is a subset `r` of the product of two sets, `C` and `D`, such that
-- each element of `C` appears as the first coordinate of *at most one* ordered pair belonging
-- to `r`.
def IsAssignmentRule {α : Type u} {β : Type v} {C : Set α} {D : Set β} (r : Set (α × β)) {hrCD : r ⊆ C ×ˢ D} : Prop 
  := ∀ c ∈ @Domain α β C D r hrCD, ∀ d ∈ @Image α β C D r hrCD, ∀ d' ∈ @Image α β C D r hrCD, ((c, d) ∈ r ∧ (c, d') ∈ r) → d = d'

-- A function is a rule of assignment `r` with a set `B` of which the image of `r` is a subset
def IsFunction {α : Type u} {β : Type v} {C : Set α} {D : Set β} (r : Set (α × β)) {hrCD : r ⊆ C ×ˢ D} (hr : @IsAssignmentRule α β C D r hrCD) (B : Set β) : Prop := @Image α β C D r hrCD ⊆ B

-- A value of a function at `a` is the unique value in `B` such that the pair `(a, b)` is a member of `r`
def IsValue {α : Type u} {β : Type v} {A : Set α} {B : Set β} {C : Set α} {D : Set β} (r : Set (α × β)) {hrCD : r ⊆ C ×ˢ D} {hr1 : @IsAssignmentRule α β C D r hrCD} (hr : @IsFunction α β C D r hrCD hr1 B) (a : α) (haA : a ∈ A) (hA : A = @Domain α β C D r hrCD) 
  := ∃! b ∈ B, (a, b) ∈ r

example {B C D : Set ℝ} (hB : B = {x : ℝ | True}) (r : Set (ℝ × ℝ)) {hrCD : r ⊆ C ×ˢ D} (hr1 : @IsAssignmentRule ℝ ℝ C D r hrCD) : IsFunction r hr1 B := by 
  rw [IsFunction, Image, Set.subset_def]
  intro x hx
  rw [hB]
  simp

section
  variable (B : Set ℝ)
  -- The far easier way to work with functions in lean is of course to use the syntax directly
  def f (a: ℝ) := a ^ 3 + 1
  #check f
  #check preimage f B
  #check f ⁻¹' B
  #check image f B
  #check f '' B

  -- You can make them anonymous like so
  #check fun (a : ℝ) ↦ a ^ 3 + 1
  #check preimage (fun (a : ℝ) ↦ a ^ 3 + 1) B
  #check (fun (a : ℝ) ↦ a ^ 3 + 1) ⁻¹' B
  #check image (fun (a : ℝ) ↦ a ^ 3 + 1) B
  #check (fun (a : ℝ) ↦ a ^ 3 + 1) '' B
end

-- a.k.a Set.restrict
def Restriction {α : Type u} {π : α → Type*} (A₀ : Set α) (f : ∀ a : α, π a) : ∀ a : A₀, π a 
  := fun x ↦ f x

def f2 (x : ℝ) := x ^ 2
def nonnegative_reals := {x : ℝ | 0 ≤ x}
section
  local notation:1000 "ℝ₊" => nonnegative_reals
  def g := Set.restrict (ℝ₊) f2
  #check g
  -- If we want to restrict the range of `f2` to `ℝ₊`, we need to use a subtype value
  theorem h_nonneg : ∀ x : ℝ, f2 x ∈ ℝ₊ := by
    intro x
    rw [f2]
    dsimp [nonnegative_reals]
    exact sq_nonneg x
  def h (x : ℝ) : ℝ₊ := ⟨f2 x, h_nonneg x⟩
  #check h
  def k := Set.restrict (ℝ₊) h
  #check k
  -- note that f2, g, h, and k are all different functions
end
