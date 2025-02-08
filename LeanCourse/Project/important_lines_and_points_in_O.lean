import LeanCourse.Project.defs
import LeanCourse.Project.lemmata_for_O
import LeanCourse.Project.two_folding_lemmata
open Classical
open Construction
open ComplexConjugate

-- **The most fundamental lines and points in 𝕆**

-- It's always useful to have a proof ready for the two most basic points to lie in 𝕆
lemma 𝕆_zero : 0 ∈ 𝕆 := by
  simp [𝕆]; use 0; simp
lemma 𝕆_one : 1 ∈ 𝕆 := by
  simp [𝕆]; use 0; simp

-- The real and imaginary axes will be used often
noncomputable def reAxis : line := O1 0 1 zero_ne_one
noncomputable def imAxis : line := O4 0 reAxis
lemma 𝕆_reAxis : reAxis ∈ 𝕆.lines := by
  exact O1_in_𝕆 𝕆_zero 𝕆_one
lemma 𝕆_imAxis : imAxis ∈ 𝕆.lines := by
  exact O4_in_𝕆 𝕆_zero 𝕆_reAxis

-- Hey, i is a great number!
lemma 𝕆_i : Complex.I ∈ 𝕆 := by
  -- first define all necessary lines and points
  let l₁ : line := O4 1 reAxis
  let l₂ : line := O3' reAxis l₁
  -- Complex.I = Isect imAxis l₂

  have I_ne_one_or_neg_one : ¬(1 = Complex.I ∨ 1 = -Complex.I) := by simp [Complex.ext_iff]
  have h5 : ¬AreParallel imAxis l₂ := by
    simp [AreParallel, line.vec, imAxis, O4, reAxis, O1, l₁, l₂, O3', Isect, I_ne_one_or_neg_one, Complex.abs, Complex.normSq]
    ring_nf; simp only [inv_eq_one_div, mul_div_assoc', neg_div', ne_eq,
      Complex.ofReal_eq_zero, Nat.ofNat_nonneg, Real.sqrt_eq_zero, OfNat.ofNat_ne_zero,
      not_false_eq_true, add_div', isUnit_iff_ne_zero, IsUnit.div_mul_cancel, eq_div_iff, sub_div']
    simp [Complex.ext_iff]

  -- Now put it all together
  have h₁ : l₁ ∈ 𝕆.lines := by exact O4_in_𝕆 𝕆_one 𝕆_reAxis
  have h₂ : l₂ ∈ 𝕆.lines := by exact O3'_in_𝕆 𝕆_reAxis h₁
  have i_eq_isect : Complex.I = Isect imAxis l₂ h5 := by
    simp [Isect, imAxis, O4, reAxis, O1, l₁, l₂, line.vec, O3', AreParallel, I_ne_one_or_neg_one, Complex.abs, Complex.normSq]
  rw [i_eq_isect]
  apply Isect_in_𝕆 𝕆_imAxis h₂
