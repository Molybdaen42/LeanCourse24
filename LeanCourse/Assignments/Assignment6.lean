/-

Assignment 6
Nora Depenheuer & Joachim Roscher

-/

import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
noncomputable section
open Real Function BigOperators Set Finset
open Classical


/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapters 7 and 8.1.
  Chapter 7 explains some of the design decisions for classes in Mathlib.

* Do the exercises corresponding to these sections in the LeanCourse/MIL folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises under "Exercises to hand-in". Deadline: 19.11.

* Make sure the file you hand-in compiles without error.
  Use sorry if you get stuck on an exercise.
-/



/-! # Exercises to practice. -/


/- Prove the following exercises about functions where the domain/codomain are
subtypes. -/

abbrev PosReal : Type := {x : ℝ // x > 0}

/- Codomain is a subtype (usually not recommended). -/
example (f : ℝ → PosReal) (hf : Monotone f) :
    Monotone (fun x ↦ log (f x)) := by {
  unfold Monotone at hf ⊢
  intro a b a_le_b
  simp
  apply (log_le_log_iff ?h1 ?h2).mpr (hf a_le_b)
  · exact (f a).property
  · exact (f b).property
  }

/- Specify that the range is a subset of a given set (recommended). -/
example (f : ℝ → ℝ) (hf : range f ⊆ {x | x > 0}) (h2f : Monotone f) :
  Monotone (log ∘ f) := by {
  unfold Monotone at h2f ⊢
  intro a b a_le_b
  simp
  apply (log_le_log_iff ?h1 ?h2).mpr (h2f a_le_b)
  · apply hf
    simp
  · apply hf
    simp
  }

/- Domain is a subtype (not recommended). -/
example (f : PosReal → ℝ) (hf : Monotone f) :
    Monotone (fun x ↦ f ⟨exp x, exp_pos x⟩) := by {
  sorry
  }

/- Only specify that a function is well-behaved on a subset of its domain (recommended). -/
example (f : ℝ → ℝ) (hf : MonotoneOn f {x | x > 0}) :
    Monotone (fun x ↦ f (exp x)) := by {
  sorry
  }



variable {G H K : Type*} [Group G] [Group H] [Group K]
open Subgroup


/- State and prove that the preimage of U under the composition of φ and ψ is a preimage
of a preimage of U. This should be an equality of subgroups! -/
example (φ : G →* H) (ψ : H →* K) (U : Subgroup K) : (ψ ∘ φ) ⁻¹' U = φ ⁻¹' (ψ ⁻¹' U) := by
  rfl

/- State and prove that the image of S under the composition of φ and ψ
is a image of an image of S. -/
example (φ : G →* H) (ψ : H →* K) (S : Subgroup G) : (ψ ∘ φ) '' S = ψ '' (φ '' S) := by
  exact image_comp ⇑ψ ⇑φ ↑S



/- Define the conjugate of a subgroup, as the elements of the form xhx⁻¹ for h ∈ H. -/
def conjugate (x : G) (H : Subgroup G) : Subgroup G where
  carrier := {x • h • x⁻¹ | h ∈ H}
  mul_mem' := by
    simp
    intro a b h1 h1_in_H x_h1_xinv_eq_a h2 h2_in_H x_h2_xinv_eq_a
    use h1 • h2
    constructor
    · exact H.mul_mem' h1_in_H h2_in_H
    · simp [← x_h1_xinv_eq_a, ← x_h2_xinv_eq_a, mul_assoc]
  one_mem' := by
    use 1
    simp
    exact H.one_mem
  inv_mem' := by
    simp
    intro h h_in_H
    use h⁻¹
    simp [mul_assoc]
    exact h_in_H


/- Now let's prove that a group acts on its own subgroups by conjugation. -/

lemma conjugate_one (H : Subgroup G) : conjugate 1 H = H := by {
  unfold conjugate
  simp
  constructor
  }

lemma conjugate_mul (x y : G) (H : Subgroup G) :
    conjugate (x * y) H = conjugate x (conjugate y H) := by {
  unfold conjugate
  simp
  ext g
  simp [mul_assoc]
  }


/- Saying that a group G acts on a set X can be done with MulAction.
The two examples below show the two properties that a group action must satisfy. -/
#print MulAction

variable (G : Type*) {X : Type*} [Group G] [MulAction G X]
example (g g' : G) (x : X) : (g * g') • x = g • (g' • x) := by exact?
example (x : X) : (1 : G) • x = x := by exact?

/- Now show that conjugate specifies a group action from G onto its subgroups. -/
instance : MulAction G (Subgroup G) where
  smul := fun g ↦ (fun g' ↦ g')
  one_smul := by
    intro b
    rfl
  mul_smul := by
    intro g g' S
    rfl


/-! # Exercises to hand-in. -/


/- A ``Setoi`d` is the name for an equivalence relation in Lean.
Let's define the smallest equivalence relation on a type ```X`. -/
def myEquivalenceRelation (X : Type*) : Setoid X where
  r x y := x = y
  iseqv := {
    refl := by intro x; rfl
    symm := by intro x y h; symm; assumption
    trans := by intro x y z x_eq_y y_eq_z; rw [x_eq_y]; assumption
  } -- Here you have to show that this is an equivalence.
                 -- If you click on the sorry, a lightbulb will appear to give the fields

/- This simp-lemma will simplify x ≈ y to x = y in the lemma below. -/
@[simp] lemma equiv_iff_eq (X : Type*) (x y : X) :
  letI := myEquivalenceRelation X; x ≈ y ↔ x = y := by rfl

/-
Now let's prove that taking the quotient w.r.t. this equivalence relation is
equivalent to the original type.

Use Quotient.mk to define a map into a quotient (or its notation ⟦_⟧)
Use Quotient.lift to define a map out of a quotient.
Use Quotient.sound to prove that two elements of the quotient are equal.
Use Quotient.ind to prove something for all elements of a quotient.
You can use this using the induction tactic: induction x using Quotient.ind; rename_i x.
-/
def quotient_equiv_subtype (X : Type*) :
    Quotient (myEquivalenceRelation X) ≃ X where
      toFun := Quotient.lift (fun x ↦ x) (by simp)
      invFun := fun x ↦ ⟦x⟧
      left_inv := by
        unfold LeftInverse
        intro x
        induction x using Quotient.ind; rename_i x
        simp
      right_inv := by
        unfold Function.RightInverse
        unfold LeftInverse
        simp


section GroupActions

variable (G : Type*) {X : Type*} [Group G] [MulAction G X]

/- Below is the orbit of an element x ∈ X w.r.t. a group action by G.
Prove that the orbits of two elements are equal
precisely when one element is in the orbit of the other. -/
def orbitOf (x : X) : Set X := range (fun g : G ↦ g • x)

lemma orbitOf_eq_iff (x y : X) : orbitOf G x = orbitOf G y ↔ y ∈ orbitOf G x := by {
  unfold orbitOf Set.range
  simp
  constructor
  · -- Suppose {z | ∃ g : G, g • x = z} = {z | ∃ g : G, g • y = z}
    intro h
    -- We need to show that y is in the first set.
    -- For this we'll show that y is in the second set.
    have h1 : y ∈ {z : X | ∃ g : G, g • y = z} := by
      use 1
      simp

    -- Now use h
    have h2 : y ∈ {z : X | ∃ g : G, g • x = z} := by
      rw [h]
      exact h1

    -- And this is it
    exact mem_setOf.mp h2

  · -- Suppose ∃ g, g • x = y
    rintro ⟨g,gx_eq_y⟩
    -- To show: {z | ∃ g : G, g • x = z} = {z | ∃ g : G, g • y = z}
    ext z
    simp
    constructor
    · -- Suppose ∃ g' : G, g' • x = z
      rintro ⟨g',g'x_eq_z⟩
      -- To show: ∃ g'' : G, g'' • y = z
      -- Let g'' = g' • g⁻¹
      use g' • g⁻¹
      -- Use that g • x = y
      rw [← gx_eq_y, smul_assoc]
      simp
      assumption
    · -- Suppose ∃ g' : G, g' • y = z
      rintro ⟨g',g'y_eq_z⟩
      -- To show: ∃ g'' : G, g'' • x = z
      -- Let g'' = g' • g
      use g' • g
      -- Use that g • x = y
      rw [← gx_eq_y, ← smul_assoc] at g'y_eq_z
      assumption
  }

/- Define the stabilizer of an element x as the subgroup of elements
g ∈ G that satisfy g • x = x. -/
def stabilizerOf (x : X) : Subgroup G where
  carrier :=
    {g : G | g • x = x}
  mul_mem' := by
    simp
    intro a b ax_eq_x bx_eq_x
    rw [← bx_eq_x, ← smul_assoc, bx_eq_x] at ax_eq_x
    assumption
  one_mem' := by
    simp
  inv_mem' := by
    simp
    intro g gx_eq_x
    rw [← gx_eq_x]
    simp
    symm
    assumption

-- This is a lemma that allows simp to simplify x ≈ y in the proof below.
@[simp] theorem leftRel_iff {x y : G} {s : Subgroup G} :
    letI := QuotientGroup.leftRel s; x ≈ y ↔ x⁻¹ * y ∈ s :=
  QuotientGroup.leftRel_apply

/- Let's probe the orbit-stabilizer theorem.

Hint: Only define the forward map (as a separate definition),
and use Equiv.ofBijective to get an equivalence.
(Note that we are coercing orbitOf G x to a (sub)type in the right-hand side) -/
def orbit_stabilizer_theorem (x : X) : G ⧸ stabilizerOf G x ≃ orbitOf G x := by {

  unfold stabilizerOf orbitOf
  -- Define the forward map f by first defining it on the domain G ...
  let f' : G → orbitOf G x := fun g ↦ {
    val := g • x
    property := by unfold orbitOf; simp
  }
  -- ... and then lift it to the quotient map f
  let f : G ⧸ stabilizerOf G x → orbitOf G x := Quotient.lift f' (by
    -- Proof that f' does the same on elements of the same equivalence class
    simp [f']
    intro a b a_equiv_b
    apply eq_inv_smul_iff.mp
    rw [← smul_assoc]
    unfold stabilizerOf at a_equiv_b
    simp at a_equiv_b
    symm
    assumption
    )

  -- use f
  apply Equiv.ofBijective f
  -- now left to show: Bijective f

  unfold Bijective; constructor
  · -- to show: Injective f
    unfold Injective
    intro g1 g2 fg1_eq_fg2
    -- treat g1 and g2 as equivalence classes
    induction g1 using Quotient.ind; rename_i g1
    induction g2 using Quotient.ind; rename_i g2

    -- simplify f ⟦g1⟧ = f ⟦g2⟧ to x = (g1⁻¹ • g2) • x
    simp [f, f'] at fg1_eq_fg2
    apply eq_inv_smul_iff.mpr at fg1_eq_fg2
    rw [← smul_assoc] at fg1_eq_fg2

    -- simplify ⟦g1⟧ = ⟦g2⟧ and realize that it's nothing different than fg1_eq_fg2
    apply Quotient.sound
    unfold stabilizerOf
    simp
    symm
    assumption

  · -- to show: Surjective f
    unfold Surjective orbitOf Set.range
    simp
    -- ∀ y : X and g : G with g • x = y we want to find g' : G s.t. f g' = y
    intro y g gx_eq_y
    -- use g because f g = g • x = y
    use g
    exact Subtype.coe_eq_of_eq_mk gx_eq_y
  }


end GroupActions
