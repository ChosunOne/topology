import Mathlib
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

open Set
open Classical

universe u v w

-- The subset of `C` such that there exists an element in `D` that the pair `(c, d)` is in `r`
-- a.k.a. the preimage of the range of the function
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
local notation:1000 "ℝ₊" => nonnegative_reals
theorem f2_nonneg : ∀ x : ℝ, f2 x ∈ ℝ₊ := by
  intro x
  rw [f2]
  dsimp [nonnegative_reals]
  exact sq_nonneg x
def g : ℝ₊ → ℝ := Set.restrict nonnegative_reals f2

section
  #check g
  #eval g ⟨2, by dsimp [nonnegative_reals]; norm_num⟩
  -- If we want to restrict the range of `f2` to `ℝ₊`, we need to use a subtype value
  def h (x : ℝ) : ℝ₊ := ⟨f2 x, f2_nonneg x⟩
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


example : ¬ (Injective f2 ∨ Surjective f2) := by 
  push_neg
  constructor
  · dsimp [Injective]
    push_neg
    use -1, 1
    constructor
    · rw [f2, f2]
      norm_num
    · norm_num
  · dsimp [Surjective]
    push_neg
    use -1
    intro a
    rw [f2]
    have ha : 0 ≤ a ^ 2 := by positivity
    intro ha2
    rw [ha2] at ha
    norm_num at ha

example : Injective g ∧ ¬ Surjective g := by 
  constructor
  · dsimp [Injective]
    intro a₁ a₂ hg
    dsimp [g] at hg
    dsimp [f2] at hg
    norm_num at hg
    apply hg
  · dsimp [Surjective]
    push_neg
    use -1
    intro a hga
    rw [g, restrict_apply] at hga
    rw [f2] at hga
    have : (0:ℝ) ≤ (a ^ 2:ℝ) := by norm_num
    have := le_trans this (by exact hga.le)
    norm_num at this

set_option pp.proofs true

example : Surjective h ∧ ¬ Injective h := by
  constructor
  · dsimp [Surjective]
    intro b
    dsimp [h]
    dsimp [f2]
    dsimp [nonnegative_reals] at b
    obtain ⟨b, hb⟩ := b
    have hsqrtb : √b ^ 2 = b := by
      exact Real.sq_sqrt hb
    use √b
    simp
    exact hsqrtb
  · dsimp [Injective]
    push_neg
    use 1, -1
    dsimp [h, f2]
    simp
    norm_num

example : Bijective k := by 
  constructor
  · dsimp[Injective]
    intro a₁ a₂ H
    dsimp [k, h] at H
    simp at H
    dsimp [f2] at H
    dsimp [nonnegative_reals] at a₁
    dsimp [nonnegative_reals] at a₂
    obtain ⟨a₁, ha₁⟩ := a₁
    obtain ⟨a₂, ha₂⟩ := a₂
    norm_cast at H
    simp at H
    apply H
  · dsimp [Surjective]
    intro b
    obtain ⟨b, hb⟩ := b
    dsimp [nonnegative_reals] at hb
    dsimp [k, h, f2]
    set b_sqrt := √b
    have hsqrtb : b_sqrt ^ 2 = b := by
      exact Real.sq_sqrt hb
    have hsqrtb_pos : 0 ≤ b_sqrt := by 
      exact Real.sqrt_nonneg b
    have hsqrtb_nonneg: b_sqrt ∈ ℝ₊ := by
      dsimp [nonnegative_reals]
      apply hsqrtb_pos
    use ⟨b_sqrt, hsqrtb_nonneg⟩ 
    simp
    exact hsqrtb

lemma two_one {α : Type u} {β : Type v} (f : α → β) (g : β → α) (h : β → α) (hgf : ∀ a : α, (g ∘ f) a = a) (hfh : ∀ b : β, (f ∘ h) b = b) : 
    Bijective f ∧ g = h ∧ Inverse f h := by 
    constructor
    · constructor
      · dsimp [Injective]
        intro a₁ a₂ H
        have h1 : (g ∘ f) a₁ = a₁ := by apply hgf
        have h2 : (g ∘ f) a₂ = a₂ := by apply hgf
        calc
          a₁ = (g ∘ f) a₁ := by rw [h1]
          _ = g (f a₁) := by rfl
          _ = g (f a₂) := by rw [H]
          _ = (g ∘ f) a₂ := by rfl
          _ = a₂ := by rw [h2]
      · dsimp [Surjective]
        intro b
        use h b
        exact hfh b
    · constructor
      · ext b
        set a₁ := g b
        set a₂ := h b
        have h1 : f a₂ = b := by
          dsimp [a₂]
          apply hfh b
        have h2 : (g ∘ f) a₂ = a₁ := by
          dsimp [a₂]
          dsimp [a₁]
          calc
            g (f (h b)) = g ((f ∘ h) b) := by rfl
            _ = g b := by exact congrArg g (hfh b)
        have h3 : (g ∘ f) a₂ = a₂ := by apply hgf
        have := by calc
          a₂ = (g ∘ f) a₂ := by rw [h3]
          _ = a₁ := by rw [h2]
        rw [this]
      · dsimp [Inverse]
        constructor
        · ext a
          simp
          set b := f a
          have h1 : (f ∘ h) b = b := by apply hfh
          have h2 : (g ∘ f) a = a := by apply hgf
          have := calc
            a = (g ∘ f) a := by rw [h2]
            _ = g (f a) := by rfl
            _ = g b := by rfl
            _ = g ((f ∘ h) b) := by rw [h1]
            _ = (g ∘ f) (h b) := by rfl
            _ = h b := by exact hgf (h b)
          rw [this]
        · ext b
          simp
          apply hfh

-- This is similar to the image of a function, but restricted to the given set
-- equivalent to `image f A₀`
-- sometimes denoted as `f(A₀)`
def SetImage {α : Type u} {β : Type v} (f : α → β) (A₀ : Set α) := { b | ∃ a, a ∈ A₀ ∧ f a = b }

#check image h {x | True}
#check SetImage h {x | True}

-- In mathlib, this is denoted by `preimage f B` or `f ⁻¹' B`
def SetPreImage {α : Type u} {β : Type v} (f : α → β) (B₀ : Set β) := { a | f a ∈ B₀ }

#check preimage h {x | True}
#check SetPreImage h {x | True}

-- Note that it is not always true that `f⁻¹' ∘ f a = a` or `f ∘ f⁻¹' b = b`

theorem image_preimage_inversion {α : Type u} {β : Type v} (f : α → β) (A₀ : Set α) (B₀ : Set β) : 
    A₀ ⊆ f⁻¹' (f '' A₀) ∧ f '' (f⁻¹' B₀) ⊆ B₀ := by 
  constructor
  · dsimp [Set.subset_def]
    intro a haA
    rw [mem_preimage, mem_image]
    use a 
  · dsimp [Set.subset_def]
    intro b hb
    rw [mem_image] at hb
    obtain ⟨x, ⟨hx, hfxb⟩⟩ := hb
    rw [mem_preimage] at hx
    rw [← hfxb]
    apply hx

-- Exercises
namespace Exercises

def α := Type u
def β := Type v
def γ := Type w

-- 1.a
example (f : α → β) (A₀ : Set α) (B₀ : Set β) (hf : Injective f) : 
  A₀ ⊆ f⁻¹' (f '' A₀) := by
  dsimp [Set.subset_def]
  intro x hxA
  use x

-- 1.b
example (f : α → β) (A₀ : Set α) (B₀ : Set β) (hf : Surjective f) : 
  f '' (f⁻¹' B₀) ⊆ B₀ := by
  dsimp [Set.subset_def]
  intro x hx
  simp at hx
  obtain ⟨x1, ⟨hfx1, hfx2⟩⟩ := hx
  rw [hfx2] at hfx1
  apply hfx1

-- 2.a
example (f : α → β) (B₀ B₁ : Set β) : 
  B₀ ⊆ B₁ → f⁻¹' B₀ ⊆ f⁻¹' B₁ := by
  intro H
  rw [Set.subset_def] at *
  intro x hx
  simp at hx
  simp
  apply H
  apply hx

-- 2.b
example (f : α → β) (B₀ B₁ : Set β) :
  f⁻¹' (B₀ ∪ B₁) = f⁻¹' B₀ ∪ f⁻¹' B₁ := by
  simp

-- 2.c
example (f : α → β) (B₀ B₁ : Set β) :
  f⁻¹' (B₀ ∩ B₁) = f⁻¹' B₀ ∩ f⁻¹' B₁ := by
  simp

-- 2.d
example (f : α → β) (B₀ B₁ : Set β) :
  f⁻¹' (B₀ \ B₁) = f⁻¹' B₀ \ f⁻¹' B₁ := by
  simp

-- 2.e
example (f : α → β) (A₀ A₁ : Set α) :
  A₀ ⊆ A₁ → f '' A₀ ⊆ f '' A₁ := by
  intro H
  rw [Set.subset_def] at *
  intro x hx
  simp
  simp at hx
  obtain ⟨x1, ⟨hx1, hx2⟩⟩ := hx
  use x1
  constructor
  · apply H
    apply hx1
  apply hx2

-- 2.f
-- a.k.a. `image_union` in Mathlib
example (f : α → β) (A₀ A₁ : Set α) : 
  f '' (A₀ ∪ A₁) = (f '' A₀) ∪ (f '' A₁) := by
  dsimp [image]
  ext x
  constructor
  · intro H
    simp at H
    obtain ⟨a, ⟨ha, hfax⟩⟩ := H
    simp
    obtain ha | ha := ha
    · left
      use a
    · right
      use a
  · intro H
    simp at H
    obtain ⟨a, ⟨ha, hfax⟩⟩ | ⟨a, ⟨ha, hfax⟩⟩ := H
    · dsimp
      use a
      constructor
      · simp
        left
        apply ha
      apply hfax
    · dsimp
      use a
      constructor
      · simp
        right
        apply ha
      apply hfax

-- 2.g
-- a.k.a. `image_inter_subset` in Mathlib
example (f : α → β) (A₀ A₁ : Set α) :
  f '' (A₀ ∩ A₁) ⊆ f '' A₀ ∩ f '' A₁ := by
  rw [Set.subset_def]
  intro b hb
  dsimp [image] at *
  simp
  obtain ⟨a, ⟨⟨haA₀, haA₁⟩, hfab⟩⟩ := hb
  constructor <;> use a

-- 2.h
example (f : α → β) (A₀ A₁ : Set α) :
  f '' A₀ \ f '' A₁ ⊆ f '' (A₀ \ A₁) := by
  rw [Set.subset_def]
  intro b hb
  obtain ⟨⟨a, ⟨haA₀, hfab⟩⟩, hnbA₁⟩ := hb
  simp at *
  use a
  constructor
  · constructor
    · apply haA₀
    intro haA₁
    apply hnbA₁ at haA₁
    contradiction
  apply hfab

-- 3.a
-- a.k.a. `preimage_iUnion₂` in Mathlib
example (f : α → β) (ℬ : Set (Set β)) :
  f⁻¹' ⋃ Bᵢ∈ ℬ, Bᵢ= ⋃ Bᵢ∈ ℬ, f⁻¹' Bᵢ := by
  simp

-- 3.b
-- a.k.a. `preimage_iInter₂` in Mathlib
example (f : α → β) (ℬ : Set (Set β)) :
  f⁻¹' ⋂ Bᵢ∈ ℬ, Bᵢ= ⋂ Bᵢ∈ ℬ, f⁻¹' Bᵢ := by
  dsimp [preimage]
  ext x
  dsimp
  constructor
  · intro hx
    simp
    intro Bᵢ hBᵢ
    simp at hx
    apply hx
    apply hBᵢ
  · intro hx
    simp at *
    apply hx

-- 3.c
-- a.k.a. `image_IUnion₂`
example (f : α → β) (𝒜 : Set (Set α)) :
  f '' ⋃ Aᵢ∈ 𝒜, Aᵢ= ⋃ Aᵢ∈ 𝒜, f '' Aᵢ := by
  ext b
  simp
  constructor
  · intro H
    obtain ⟨a, ⟨⟨A, ⟨hA𝒜, haA⟩⟩, hfab⟩⟩ := H
    use A
    constructor
    · apply hA𝒜
    · use a
  · intro H
    obtain ⟨A, ⟨hA𝒜 , ⟨a, ⟨haA, hfab⟩⟩⟩⟩ := H
    use a
    constructor
    · use A
    · apply hfab

-- 3.d
-- a.k.a. `image_iInter₂_subset` in Mathlib
example (f : α → β) (𝒜 : Set (Set α)) (h𝒜 : 𝒜 ≠ ∅) :
  f '' ⋂ Aᵢ∈ 𝒜 , Aᵢ ⊆ ⋂ Aᵢ∈ 𝒜, f '' Aᵢ:= by
  rw [Set.subset_def]
  intro b hb
  rw [← nonempty_iff_ne_empty, Set.nonempty_def] at h𝒜 
  obtain ⟨A, hA⟩ := h𝒜 
  simp at *
  obtain ⟨a, ⟨hA𝒜, hfab⟩⟩ := hb
  intro A hA
  use a
  constructor
  · apply hA𝒜 
    apply hA
  apply hfab

-- 4.a
example (f : α → β) (g : β → γ) (C₀ : Set γ) :
  (g ∘ f)⁻¹' C₀ = f⁻¹' (g⁻¹' C₀) := by
  ext a
  constructor
  · intro ha
    simp at *
    apply ha
  · intro ha
    simp at *
    apply ha

-- 4.b
example (f : α → β) (g : β → γ) (hf : Injective f) (hg : Injective g) :
  Injective (g ∘ f) := by
  dsimp [Injective] at *
  intro a₁ a₂ H
  have : g (f a₁) = g (f a₂) → f a₁ = f a₂ := by apply hg
  apply this at H
  apply hf
  apply H

-- 4.c
-- What can you say with the following hypotheses regarding the injectivity of g and f?
-- We can easily prove the injectivity of f, but we can't say anything about the injectivity
-- of g because the range of f may not cover the domain of g (Surjectivity of f).
example (f : α → β) (g : β → γ) (hfg : Injective (g ∘ f)) : Injective f := by
  dsimp [Injective] at *
  intro a₁ a₂ H
  have : g (f a₁) = g (f a₂) → a₁ = a₂ := by apply hfg
  apply this
  rw [H]

-- 4.d
example (f : α → β) (g : β → γ) (hf : Surjective f) (hg : Surjective g) :
    Surjective (g ∘ f) := by
  dsimp [Surjective] at *
  intro c
  have : ∃ b, g b = c := by apply hg
  obtain ⟨b, hgbc⟩ := this
  have : ∃ a, f a = b := by apply hf
  obtain ⟨a, hfab⟩ := this
  use a
  rw [hfab, hgbc]

-- 4.e
-- What can you say with the following hypotheses regarding the surjectivity of g and f?
-- We can prove the Surjectivity of g but not f since the Injectivity of g is not known
example (f : α → β) (g : β → γ) (hfg : Surjective (g ∘ f)) : Surjective g := by
  dsimp [Surjective] at *
  intro c
  have : ∃ a, g (f a) = c := by apply hfg
  obtain ⟨a, hgfac⟩ := this
  use f a

-- 4.f
-- Write a theorem summarizing the results from 4.b-e
example (f : α → β) (g : β → γ) : Bijective (g ∘ f) → Injective f ∧ Surjective g := by
  intro H
  dsimp [Bijective] at H
  obtain ⟨h_inj, h_surj⟩ := H
  have hf_inj : Injective f := by
    dsimp [Injective] at *
    intro a₁ a₂ H
    have : g (f a₁) = g (f a₂) → a₁ = a₂ := by apply h_inj
    apply this
    rw [H]
  have hg_surj : Surjective g := by
    dsimp [Surjective] at *
    intro c
    have : ∃ a, g (f a) = c := by apply h_surj
    obtain ⟨a, hgfac⟩ := this
    use f a
  constructor
  · apply hf_inj
  · apply hg_surj

-- 5.a
def LeftInverse {α : Type u} {β : Type v} (f : α → β) (g : β → α) := g ∘ f = id
def RightInverse' {α : Type u} {β : Type v} (f : α → β) (h : β → α) := f ∘ h = id

example (f : α → β) (g : β → α) (hg : LeftInverse f g) : Injective f := by
  dsimp [LeftInverse] at hg
  dsimp [Injective]
  intro a₁ a₂ h
  let ga₁ := g (f a₁)
  let ga₂ := g (f a₂)
  have hga₁ : ga₁ = a₁ := by 
    dsimp [ga₁]
    calc
      g (f a₁) = (g ∘ f) a₁ := by rfl
      _ = id a₁ := by rw [hg]
      _ = a₁ := by rfl
  have hga₂ : ga₂ = a₂ := by 
    dsimp [ga₂]
    calc
      g (f a₂) = (g ∘ f) a₂ := by rfl
      _ = id a₂ := by rw [hg]
      _ = a₂ := by rfl
  calc
    a₁ = ga₁ := by rw [hga₁]
    _ = g (f a₁) := by dsimp
    _ = g (f a₂) := by rw [h]
    _ = ga₂ := by dsimp
    _ = a₂ := by rw [hga₂]


example (f : α → β) (h : β → α) (hh : RightInverse' f h) : Surjective f := by
  dsimp [Surjective]
  intro b
  dsimp [RightInverse'] at hh
  use h b
  calc
    f (h b) = (f ∘ h) b := by rfl
    _ = id b := by rw [hh]

-- 5.b
def f_no_right_inverse (x : ℕ) : ℕ := 2 ^ x

#eval f_no_right_inverse 3
#eval Nat.log2 (f_no_right_inverse 3)

example : ∃ g : ℕ → ℕ, LeftInverse f_no_right_inverse g := by
  use fun x => Nat.log2 x
  dsimp [LeftInverse]
  ext x
  dsimp [f_no_right_inverse]
  simp

example : ¬∃ h : ℕ → ℕ, RightInverse' f_no_right_inverse h := by
  dsimp [RightInverse']
  push_neg
  intro h H
  have hf_nri : ∀ x : ℕ, 1 ≤ f_no_right_inverse x := by
    intro x
    dsimp [f_no_right_inverse]
    exact Nat.one_le_two_pow
  have hf_nri_2 : ¬∃ x : ℕ, f_no_right_inverse x < 1 := by
    push_neg
    apply hf_nri
  apply hf_nri_2
  use h 0
  calc
    f_no_right_inverse (h 0) = (f_no_right_inverse ∘ h) 0 := by rfl
    _ = id 0 := by rw [H]
    _ = 0 := by rfl
  norm_num

-- 5.c
def f_no_left_inverse (a : ℕ) : ℕ := Nat.log2 a

#eval (f_no_left_inverse 1)
#eval f_no_left_inverse (2 ^ 0)

example : ∃ h : ℕ → ℕ, RightInverse' f_no_left_inverse h := by
  use fun x => 2 ^ x
  ext x
  dsimp [f_no_left_inverse]
  simp

example : ¬∃ g : ℕ → ℕ, LeftInverse f_no_left_inverse g := by
  dsimp [LeftInverse]
  intro ⟨g, hg⟩ 
  have : ∃ x y: ℕ, f_no_left_inverse x = f_no_left_inverse y ∧ x ≠ y := by
    use 0, 1 
    constructor
    · dsimp [f_no_left_inverse]
      unfold Nat.log2
      simp
    · norm_num
  obtain ⟨x, ⟨y, ⟨hfxy, hxy⟩⟩⟩ := this
  apply hxy
  calc
    x = id x := by rfl
    _ = (g ∘ f_no_left_inverse) x := by rw [hg]
    _ = g (f_no_left_inverse x) := by rfl
    _ = g (f_no_left_inverse y) := by rw [hfxy]
    _ = (g ∘ f_no_left_inverse) y := by rfl
    _ = id y := by rw [hg]
    _ = y := by rfl

-- 5.d
-- The question is open ended, so it suffices to show one scenario in which there can be multiple distinct left inverses.  The answer here will demonstrate that, though it remains open whether or not the injectivity of g is a 
-- necessary condition.
-- We can definitely show that if f is not surjective but g is injective, there can be more than one left inverse
example (f : α → β) (g : β → α) (hg : LeftInverse f g) (hg2 : Injective g) (hf_nsurj : ¬ Surjective f) : ∃ h : β → α, LeftInverse f h ∧ h ≠ g := by
  dsimp [LeftInverse, Surjective] at *
  push_neg at *
  obtain ⟨b, hb⟩ := hf_nsurj
  let c := g b
  let d := f c
  have hdnb : d ≠ b := by
    dsimp [d]
    apply hb
  use fun x => if x = b then g d else g x
  constructor
  · ext a
    simp
    split_ifs with hfab
    · have : f a ≠ b := by apply hb
      contradiction
    calc
      g (f a) = (g ∘ f) a := by rfl
      _ = id a := by rw [hg]
  · simp
    rw [funext_iff]
    push_neg
    use b
    split_ifs with H
    · intro this
      apply hg2 at this
      contradiction
    · contradiction

-- We can definitely show that if f is surjective, there cannot be more than one left inverse
example (f : α → β) (g : β → α) (hg : LeftInverse f g) (hf_surj : Surjective f) : ¬∃ h : β → α, LeftInverse f h ∧ h ≠ g := by
  intro H
  obtain ⟨h, ⟨hfh, hhg⟩⟩ := H
  have : ∃ b : β, h b ≠ g b := by
    exact Function.ne_iff.mp hhg
  obtain ⟨b, hb⟩ := this
  dsimp [LeftInverse] at *
  dsimp [Surjective] at *
  have : ∃ a, f a = b := by apply hf_surj
  obtain ⟨a, hfab⟩ := this
  apply hb
  calc
    h b = h (f a) := by rw [hfab]
    _ = (h ∘ f) a := by rfl
    _ = id a := by rw [hfh]
    _ = (g ∘ f) a := by rw [hg]
    _ = g (f a) := by rfl
    _ = g b := by rw [hfab]

example (f : α → β) (g : β → α) (hg : RightInverse' f g) : ∃ h : β → α, RightInverse' f h ∧ h ≠ g := by
  sorry

example (f : α → β) (g : β → α) (hg : RightInverse' f g) : ¬∃ h : β → α, RightInverse' f h ∧ h ≠ g := by
  sorry

-- 5.e
example (f : α → β) (g h : β → α) (hg : LeftInverse f g) (hh : RightInverse' f h) : Bijective f ∧ g = h ∧ Inverse f h := by
  sorry

-- 6.
-- Fill out function `g` by restricting `f` appropriately
def f (x : ℝ) := x ^ 3 - x

def g (x : sorry) : sorry := sorry

example : Bijective g := by 
  sorry

end Exercises
