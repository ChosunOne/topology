import Mathlib
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

open Set

universe u v w

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
  #eval g ⟨2, by dsimp [nonnegative_reals]; norm_num⟩
  -- If we want to restrict the range of `f2` to `ℝ₊`, we need to use a subtype value
  theorem h_nonneg : ∀ x : ℝ, f2 x ∈ ℝ₊ := by
    intro x
    rw [f2]
    dsimp [nonnegative_reals]
    exact sq_nonneg x
  def h (x : ℝ) : ℝ₊ := ⟨f2 x, h_nonneg x⟩
  #check h
  #eval h 2
  def k := Set.restrict (ℝ₊) h
  #check k
  #eval k ⟨2, by dsimp [nonnegative_reals]; norm_num⟩
  -- note that f2, g, h, and k are all different functions
end

-- a.k.a. the `∘` operator
def composition {α : Type u} {β : Type v} {γ : Type w} (f : α → β) (g : β → γ) := fun x => g (f x) 
def f3 (x : ℤ) : ℚ := x
def g2 (x : ℚ) : ℝ := x

#check composition f3 g2
#check g2 ∘ f3

def f4 (x : ℝ) := 3 * x ^ 2 + 2
def g3 (x : ℝ) := 5 * x
def h2 (x : ℝ) := 5 * (3 * x ^ 2 + 2)
def h3 (x : ℝ) := 3 * (5 * x) ^ 2 + 2

example : g3 ∘ f4 = h2 := by 
  ext x
  rfl

example : f4 ∘ g3 = h3 := by
  ext x
  rfl

-- note that h2 and h3 are different functions

-- Meaning that if two outputs are the same, the inputs must be the same
-- a.k.a. a 1:1 mapping
-- This can be imported from Mathlib `Function`
def Injective {α : Type u} {β : Type v} (f : α → β) : Prop :=
  ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂

-- Meaning that for members of B, there is an output of f from A that produces the member of B
-- a.k.a. "A maps onto B"
-- This can be imported from Mathlib `Function`
def Surjective {α : Type u} {β : Type v} (f : α → β) : Prop :=
  ∀ b, ∃ a, f a = b

-- a.k.a. a 1:1 correspondance (bi-directional 1:1 mapping)
-- This can be imported from Mathlib `Function`
def Bijective {α : Type u} {β : Type v} (f : α → β) : Prop := 
  Injective f ∧ Surjective f

def Inverse {α : Type u} {β : Type v} (f : α → β) (g : β → α) : Prop := g ∘ f = id ∧ f ∘ g = id

theorem exists_inverse_of_bijective {α : Type u} {β : Type v} (f : α → β) (hf : Bijective f) : ∃ g, Inverse f g := by
  dsimp [Bijective] at hf
  obtain ⟨hf_inj, hf_surj⟩ := hf
  dsimp [Inverse]
  choose g hg using hf_surj
  use g
  constructor
  · ext x
    exact hf_inj (hg (f x)) 
  · ext x
    exact hg x

theorem inverse_of_bijective_is_bijective {α : Type u} {β : Type v} (f : α → β) (hf : Bijective f) (f_inv : β → α) (hf_inv : Inverse f f_inv) : Bijective f_inv := by
  constructor
  · intro a₁ a₂ H
    obtain ⟨hf_inj, hf_surj⟩ := hf
    have h1 := hf_surj a₁
    have h2 := hf_surj a₂ 
    obtain ⟨a, hfa⟩ := h1
    obtain ⟨b, hfb⟩ := h2
    rw [← hfa, ← hfb]
    obtain ⟨h3, h4⟩ := hf_inv
    have hafi : a = f_inv a₁ := by
      calc
        a = id a := by rfl
        _ = (f_inv ∘ f) a  := by rw [h3]
        _ = f_inv (f a) := by rfl
        _ = f_inv a₁ := by rw [hfa]
    have hbfi : b = f_inv a₂ := by
      calc
        b = id b := by rfl
        _ = (f_inv ∘ f) b := by rw [h3]
        _ = f_inv (f b) := by rfl
        _ = f_inv a₂ := by rw [hfb]
    rw [← hafi, ← hbfi] at H
    rw [H]
  · intro b
    obtain ⟨hf_inj, hf_surj⟩ := hf
    use f b
    obtain ⟨hfif, hffi⟩ := hf_inv
    have := by calc
      f_inv (f b) = (f_inv ∘ f) b := by rfl
      _ = id b := by rw [hfif] 
      _ = b := by rfl
    apply this

