import LeanCourse.Project.defs
import LeanCourse.Project.lemmata_for_O
import LeanCourse.Project.two_folding_lemmata
open Classical
open Construction
open ComplexConjugate

-- **The most fundamental lines and points in 𝕆**

lemma zero_in_𝕆 : 0 ∈ 𝕆 := by
  simp [𝕆]; use 0; simp
lemma one_in_𝕆 : 1 ∈ 𝕆 := by
  simp [𝕆]; use 0; simp

noncomputable def reAxis : line := O1 0 1 zero_ne_one
noncomputable def imAxis : line := O4 0 reAxis
lemma reAxis_in_𝕆 : reAxis ∈ 𝕆.lines := by
  exact O1_in_𝕆 zero_in_𝕆 one_in_𝕆
lemma imAxis_in_𝕆 : imAxis ∈ 𝕆.lines := by
  exact O4_in_𝕆 zero_in_𝕆 reAxis_in_𝕆

lemma i_in_𝕆 : Complex.I ∈ 𝕆 := by
  -- first define all necessary lines and points
  let l₁ : line := O4 1 reAxis
  let l₂ : line := O3' reAxis l₁
  -- Complex.I = Isect imAxis l₂

  have I_ne_one_or_neg_one : ¬(1 = Complex.I ∨ 1 = -Complex.I) := by simp [Complex.ext_iff]
  have h5 : ¬AreParallel imAxis l₂ := by
    simp [AreParallel, line.vec, imAxis, O4, reAxis, O1, l₁, l₂, O3', Isect, I_ne_one_or_neg_one, Complex.abs, Complex.normSq]
    ring_nf; field_simp
    constructor
    · simp [Complex.ext_iff]
      intro h; exfalso
      obtain h' := Ne.symm ((fun {x} ↦ Real.sqrt_ne_zero'.mpr) zero_lt_two)
      contradiction
    · simp [Complex.ext_iff]

  -- Now put it all together
  have h₁ : l₁ ∈ 𝕆.lines := by exact O4_in_𝕆 one_in_𝕆 reAxis_in_𝕆
  have h₂ : l₂ ∈ 𝕆.lines := by exact O3'_in_𝕆 reAxis_in_𝕆 h₁
  have i_eq_isect : Complex.I = Isect imAxis l₂ h5 := by
    simp [Isect, imAxis, O4, reAxis, O1, l₁, l₂, line.vec, O3', AreParallel, I_ne_one_or_neg_one, Complex.abs, Complex.normSq]
  rw [i_eq_isect]
  apply Isect_in_𝕆 imAxis_in_𝕆 h₂
