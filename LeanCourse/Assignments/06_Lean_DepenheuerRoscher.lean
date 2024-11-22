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

/-! # Exercises to hand-in. -/


/- A Setoid is the name for an equivalence relation in Lean.
Let's define the smallest equivalence relation on a type X. -/
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
