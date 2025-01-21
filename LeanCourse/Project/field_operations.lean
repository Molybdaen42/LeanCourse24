import LeanCourse.Project.defs
import LeanCourse.Project.lemmata_for_O
import LeanCourse.Project.important_lines_and_points_in_O
import LeanCourse.Project.two_folding_lemmata
import Mathlib.Algebra.Field.Defs
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Algebra.CubicDiscriminant
open Classical
open Construction
open ComplexConjugate

/- **Field Operations** -/

section add

theorem 𝕆_neg {z : ℂ} (hz : z ∈ 𝕆) : -z ∈ 𝕆 := by
  -- W.l.o.g. z ≠ 0
  by_cases z_ne_zero : z = 0; simp [z_ne_zero]; exact zero_in_𝕆

  -- Idea: Mirror z across the perpendicular line sitting at 0.
  let l₁ := O1 z 0 z_ne_zero
  have hl₁ : l₁ ∈ 𝕆.lines := O1_in_𝕆 hz zero_in_𝕆

  let l₂ := O4 0 l₁
  have hl₂ : l₂ ∈ 𝕆.lines := O4_in_𝕆 zero_in_𝕆 hl₁
  have hl₂_z₁ : l₂.z₁ = 0 := by simp [l₂, O4]
  have hl₂_z₂ : l₂.z₂ = -Complex.I * z / Complex.abs z := by
    simp [l₂, O4, line.vec, l₁, O1]
    ring
  have hl₂_vec : l₂.vec = -Complex.I * z / Complex.abs z := by
    simp [line.vec, hl₂_z₁, hl₂_z₂, div_abs z_ne_zero, neg_div]

  apply in_𝕆_if_eq (E2 z l₂)
  · exact E2_in_𝕆 z l₂ hz hl₂
  simp [E2, hl₂_z₁, hl₂_vec]
  ring_nf

lemma 𝕆_double {z : ℂ} (hz : z ∈ 𝕆) : 2 * z ∈ 𝕆 := by
  -- W.l.o.g. z ≠ 0
  by_cases z_ne_zero : z = 0; simp [z_ne_zero]; exact zero_in_𝕆

  -- Idea: Mirror the 0 across the perpendicular line sitting at z.
  let l₁ := O1 z 0 z_ne_zero
  have hl₁ : l₁ ∈ 𝕆.lines := O1_in_𝕆 hz zero_in_𝕆

  let l₂ := O4 z l₁
  have hl₂ : l₂ ∈ 𝕆.lines := O4_in_𝕆 hz hl₁
  have hl₂_z₁ : l₂.z₁ = z := by simp [l₂, O4]
  have hl₂_z₂ : l₂.z₂ = z - Complex.I * z / Complex.abs z := by
    simp [l₂, O4, line.vec, l₁, O1]
    ring
  have hl₂_vec : l₂.vec = -Complex.I * z / Complex.abs z := by
    simp [line.vec, hl₂_z₁, hl₂_z₂, div_abs z_ne_zero, neg_div]

  apply in_𝕆_if_eq (E2 0 l₂)
  · exact E2_in_𝕆 0 l₂ zero_in_𝕆 hl₂
  simp [E2, hl₂_z₁, hl₂_vec, z_ne_zero]
  ring_nf

lemma 𝕆_add_multiples {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ 𝕆) (hz₂ : z₂ ∈ 𝕆) (h_multiple : ∃ a : ℝ, z₁ = a * z₂) : z₁ + z₂ ∈ 𝕆 := by
  obtain ⟨a,ha⟩ := h_multiple
  -- Here is the proof why we can assume w.l.o.g. that |z₁| < |z₂| holds.
  by_cases h_abs_ne : z₁ = z₂ ∨ z₁ = -z₂
  · -- The case that z₁ = ±z₂,
    -- therefore their sum equals 0 or 2 * z₁. Apply zero_in_𝕆 or 𝕆_double.

    simp [ha] at h_abs_ne
    rcases h_abs_ne with a_one|a_neg_one
    · -- a = 1
      simp [ha, a_one, ← two_mul]
      exact 𝕆_double hz₂
    · -- a = -1
      simp [ha, a_neg_one, ← two_mul]
      exact zero_in_𝕆
  · -- The case that z₁ ≠ ±z.
    have hz₁_ne_z₂ : z₁ ≠ z₂ := by
      by_contra h
      simp [h] at h_abs_ne
    have hz₁_ne_neg_z₂ : z₁ ≠ -z₂ := by
      by_contra h
      simp [h] at h_abs_ne
    by_cases hz₁_ne_zero : z₁ = 0; · simp [hz₁_ne_zero, hz₂]
    by_cases hz₂_ne_zero : z₂ = 0; · simp [hz₂_ne_zero, hz₁]
    by_cases hz₁_ne_h₂ : z₁ = z₂; rw [← hz₁_ne_h₂,← two_mul]; apply 𝕆_double hz₁
    push_neg at hz₁_ne_zero hz₂_ne_zero

    -- First mark the line l₁ passing through 0, z₁ and z₂.
    let l₁ := O1 z₁ 0 hz₁_ne_zero
    have hl₁ : l₁ ∈ 𝕆.lines := O1_in_𝕆 hz₁ zero_in_𝕆

    -- Next, we fold z₂ onto z₁ using O2.
    let l₂ := O2 z₁ z₂ hz₁_ne_z₂
    have hl₂ : l₂ ∈ 𝕆.lines := O2_in_𝕆 hz₁ hz₂

    -- Now, let's mirror 0 across l₂ and get z₁+z₂
    apply in_𝕆_if_eq (E2 0 l₂)
    · exact E2_in_𝕆 0 l₂ zero_in_𝕆 hl₂
    simp [E2, l₂, O2, line.vec, ha]
    ring_nf

/--𝕆 is closed under addition.-/
theorem 𝕆_add {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ 𝕆) (hz₂ : z₂ ∈ 𝕆) : z₁ + z₂ ∈ 𝕆 := by
  -- Wlog we can assume that z₁ and z₂ are not equal to 0 or to a multiple (by a real number) of each other
  by_cases hz₁_ne_zero : z₁ = 0; simp [hz₁_ne_zero, hz₂]
  by_cases hz₂_ne_zero : z₂ = 0; simp [hz₂_ne_zero, hz₁]
  by_cases hz₁_ne_real_mult_z₂ : ∃ a : ℝ, z₁ = a * z₂
  · exact 𝕆_add_multiples hz₁ hz₂ hz₁_ne_real_mult_z₂
  push_neg at hz₁_ne_zero hz₂_ne_zero hz₁_ne_real_mult_z₂

  -- ToDo: Wollen wir noch den folgenden Fall per oBdA annehmen?
  --hz₁_ne_z₂_normalised : z₁/(Complex.abs z₁) ≠ z₂/(Complex.abs z₂)

  -- First step: create two lines from 0 to z₁ resp. z₂.
  let l₁ := O1 0 z₁ hz₁_ne_zero.symm
  let l₂ := O1 0 z₂ hz₂_ne_zero.symm
  have hl₁ : l₁ ∈ 𝕆.lines := O1_in_𝕆 zero_in_𝕆 hz₁
  have hl₂ : l₂ ∈ 𝕆.lines := O1_in_𝕆 zero_in_𝕆 hz₂

  -- Second step: fold a line parallel to l₁ that goes through z₂
  -- and a line parallel to l₂ that goes through z₁.
  let l₃ := E1 z₂ l₁
  let l₄ := E1 z₁ l₂
  have hl₃ : l₃ ∈ 𝕆.lines := E1_in_𝕆 z₂ l₁ hz₂ hl₁
  have hl₄ : l₄ ∈ 𝕆.lines := E1_in_𝕆 z₁ l₂ hz₁ hl₂
  have hl₃_z₁ : l₃.z₁ = z₂                       := by simp [l₃, E1]
  have hl₃_z₂ : l₃.z₂ = z₂ - z₁ / Complex.abs z₁ := by simp [l₃, E1, l₁, O1, line.vec]
  have hl₄_z₁ : l₄.z₁ = z₁                       := by simp [l₄, E1]
  have hl₄_z₂ : l₄.z₂ = z₁ - z₂ / Complex.abs z₂ := by simp [l₄, E1, l₂, O1, line.vec]

  have hl₃_l₄_not_parallel : ¬AreParallel l₃ l₄ := by
    simp_rw [AreParallel, line.vec, hl₃_z₁, hl₃_z₂, hl₄_z₁, hl₄_z₂]
    simp [div_self, hz₁_ne_zero, hz₂_ne_zero]
    constructor
    · specialize hz₁_ne_real_mult_z₂ ((Complex.abs z₁)/Complex.abs z₂)
      by_contra h
      simp [div_mul_comm, ← h, div_mul, div_self, hz₁_ne_zero] at hz₁_ne_real_mult_z₂
    · specialize hz₁_ne_real_mult_z₂ (-(Complex.abs z₁)/Complex.abs z₂)
      by_contra h
      simp [div_mul_comm, ← h, div_mul, div_self, hz₁_ne_zero] at hz₁_ne_real_mult_z₂

  -- Last step: take the intersection of l₃ and l₄.
  apply in_𝕆_if_eq (Isect l₃ l₄ hl₃_l₄_not_parallel)
  · exact Isect_in_𝕆 hl₃ hl₄
  · -- to show: this intersection really is the searched sum
    simp [Isect, line.vec, hl₃_z₁, hl₃_z₂, hl₄_z₁, hl₄_z₂, div_self, hz₁_ne_zero, hz₂_ne_zero]
    simp [div_mul_eq_mul_div, neg_div', div_add_div_same, mul_div_assoc', div_div, div_div_eq_mul_div]
    rw [mul_assoc (Complex.abs z₂ : ℂ), mul_comm ((-((z₂.re : ℂ) * z₁.im) + (z₂.im : ℂ) * z₁.re))]
    rw [mul_comm (Complex.abs z₂ : ℂ),  ← mul_assoc (Complex.abs z₂ : ℂ), ← mul_assoc, mul_comm, mul_div_assoc, ← div_div, ← div_div, mul_div_assoc, div_abs hz₂_ne_zero, mul_one]
    rw [mul_div_assoc, div_abs hz₁_ne_zero, mul_one]
    ring_nf
    simp
    symm
    simp only [inv_eq_one_div, mul_div_assoc', mul_one]
    have : (z₂.im : ℂ) * (z₁.re : ℂ) - (z₂.re : ℂ) * (z₁.im : ℂ) ≠ 0 := by
      norm_cast
      push_neg
      -- Why is it important for z₁ and z₂ to be non-orthogonal?
      by_cases hz₂_re_ne_zero: z₂.re ≠ 0;
        · by_contra h
          specialize hz₁_ne_real_mult_z₂ (z₁.re/z₂.re)
          have : z₁.re=(z₁.re/z₂.re)*z₂.re := by
            rw [div_mul_comm, div_self hz₂_re_ne_zero]
            ring_nf
          simp [Complex.ext_iff] at hz₁_ne_real_mult_z₂
          apply hz₁_ne_real_mult_z₂
          exact this
          rw [sub_eq_iff_eq_add, add_comm, add_zero,mul_comm z₂.re, ← div_eq_iff] at h
          rw[← h]
          ring_nf
          exact hz₂_re_ne_zero
      push_neg at hz₂_re_ne_zero
      rw[hz₂_re_ne_zero]
      simp
      have : z₂.im≠ 0 := by
          simp [Complex.ext_iff] at hz₂_ne_zero
          apply hz₂_ne_zero
          exact hz₂_re_ne_zero
      constructor
      · exact this
      · by_contra h
        specialize hz₁_ne_real_mult_z₂ (z₁.im/z₂.im)
        simp [Complex.ext_iff] at hz₁_ne_real_mult_z₂
        apply hz₁_ne_real_mult_z₂
        · rw[hz₂_re_ne_zero,h]
          ring_nf
        rw [div_mul_comm, div_self this]
        ring_nf
    calc
      _ = z₁ * ((↑z₂.im * ↑z₁.re - ↑z₂.re * ↑z₁.im) / (↑z₂.im * ↑z₁.re - ↑z₂.re * ↑z₁.im) )
             := by ring
      _ = z₁ := by simp [div_self this]

end add
section mul

lemma 𝕆_real_mul_cmpl {a z : ℂ} (ha_real : a.im = 0) (ha : (a:ℂ) ∈ 𝕆) (hz_not_real : z.im ≠ 0) (hz : z ∈ 𝕆) : a * z ∈ 𝕆 := by
  --defining the lines from z to 0 and 1, not parallel which is why z not be real
  have z_ne_zero: z ≠ 0 := by simp [Complex.ext_iff, hz_not_real]
  have z_abs_ne_zero : Complex.abs z ≠ 0 := by simp[sub_ne_zero_of_ne z_ne_zero]; push_neg; exact z_ne_zero;
  let l₁ := O1 0 z z_ne_zero.symm
  have l₁_in_𝕆 : l₁ ∈ 𝕆.lines := by exact O1_in_𝕆 zero_in_𝕆 hz
  have l₁_vec : l₁.vec = z/Complex.abs z := by simp[line.vec,l₁, O1]
  have z_ne_one: z ≠ 1 := by simp [Complex.ext_iff, hz_not_real]
  have z_abs_ne_one : Complex.abs (z-1) ≠ 0 := by simp[sub_ne_zero_of_ne z_ne_zero]; push_neg; exact z_ne_one;
  let l₂ := O1 1 z z_ne_one.symm
  have l₂_vec : l₂.vec = (z-1)/Complex.abs (z-1) := by simp[line.vec,l₂, O1]
  have l₂_in_𝕆 : l₂ ∈ 𝕆.lines := by exact O1_in_𝕆 one_in_𝕆 hz
  have l₁_l₂_not_parallel : ¬AreParallel l₁ l₂ := by
    unfold AreParallel
    push_neg
    constructor
    · simp [l₁_vec, l₂_vec, Complex.ext_iff]
      · intro h
        by_contra h'
        have := mul_eq_mul_of_div_eq_div z.im z.im z_abs_ne_zero z_abs_ne_one h'
        have := mul_left_cancel₀ hz_not_real this
        rw[this] at h
        have := mul_eq_mul_of_div_eq_div z.re (z.re-1) z_abs_ne_zero z_abs_ne_zero h
        have := mul_right_cancel₀ z_abs_ne_zero this
        linarith
    · simp [l₁_vec, l₂_vec, Complex.ext_iff]
      · intro h
        by_contra h'
        rw[← neg_div] at h'
        have := mul_eq_mul_of_div_eq_div z.im (-z.im) z_abs_ne_zero z_abs_ne_one h'
        rw[neg_mul_comm] at this
        have := mul_left_cancel₀ hz_not_real this
        rw[this, div_neg, neg_neg] at h
        have := mul_eq_mul_of_div_eq_div z.re (z.re-1) z_abs_ne_zero z_abs_ne_zero h
        have := mul_right_cancel₀ z_abs_ne_zero this
        linarith
  --defining the line parallel to l₂ going through a
  let l₃ := E1 a l₂
  have l₃_in_𝕆 : l₃ ∈ 𝕆.lines := by exact E1_in_𝕆 a l₂ ha l₂_in_𝕆
  --helps a  lot with the computations
  have : Complex.abs (z-1) ≠ 0 := by simp[sub_ne_zero_of_ne z_ne_one]; push_neg; exact z_ne_one;
  have l₃_vec : l₃.vec = (1-z)/Complex.abs (z-1) := by
    simp [l₃,line.vec, E1,l₂, O1]
    norm_cast
    simp [div_self this,← neg_div]
  have l₂_l₃_parallel : AreParallel l₂ l₃ := by
    exact (E1_in_𝕆'' a l₂ ha l₂_in_𝕆).2.2
  have l₁_l₃_not_parallel : ¬AreParallel l₁ l₃ := by
    exact Not_parallel_if_parallel l₁ l₂ l₃ l₁_l₂_not_parallel l₂_l₃_parallel
  --define the intersection of l₁ l₃
  let z₂ := Isect l₁ l₃ l₁_l₃_not_parallel
  --z₂ should be a*z
  apply in_𝕆_if_eq z₂
  exact Isect_in_𝕆 l₁_in_𝕆 l₃_in_𝕆
  --use all definitions
  simp [z₂, Isect, l₁_vec,l₃_vec, l₃,E1, l₂_vec,line.vec,l₂,O1,l₁,O1]
  norm_cast
  --just calculate
  simp[← neg_div, div_self this, ← neg_mul, ha_real]
  have a_re : a = a.re := by simp [Complex.ext_iff, ha_real]
  have : (((-z.im * Complex.abs (z - 1) * Complex.abs z) / (-z.im * Complex.abs (z - 1) * Complex.abs z)):ℂ) = 1 := by
    apply div_self
    simp[div_self this, z_ne_one, z_ne_zero, hz_not_real]
  calc
    _ = a*z*(-z.im*(Complex.abs (z-1))*(Complex.abs z))/(-z.im*(Complex.abs (z-1))*(Complex.abs z))
      :=  by rw[mul_div_assoc, this];ring
    _ = -z.im/(Complex.abs (z-1))*a*((Complex.abs (z-1))*(Complex.abs z)/(-z.im))*z/(Complex.abs z)
      := by ring
    _ = -z.im/(Complex.abs (z-1))*a*((-z.im)/((Complex.abs (z-1))*(Complex.abs z)))⁻¹*z/(Complex.abs z)
      := by simp[inv_inv_div_inv]
    _ = -z.im/(Complex.abs (z-1))*a/((-z.im)/((Complex.abs (z-1))*(Complex.abs z)))*z/(Complex.abs z)
      := by simp [div_eq_mul_inv];
    _ = -z.im/(Complex.abs (z-1))*a/((-z.im)/((Complex.abs (z-1))*(Complex.abs z))+z.re*z.im/((Complex.abs (z-1))*(Complex.abs z))-z.re*z.im/((Complex.abs (z-1))*(Complex.abs z)))*z/(Complex.abs z) := by ring
    _ = -z.im / (Complex.abs (z - 1)) * a /((1 - z.re) / (Complex.abs (z - 1)) * (-z.im / (Complex.abs z)) +-z.im / ↑(Complex.abs (z - 1)) * (z.re / (Complex.abs z))) *(z /(Complex.abs z))
      := by ring
    _ = -↑z.im / ↑(Complex.abs (z - 1)) * ↑a.re /
      ((1 - ↑z.re) / ↑(Complex.abs (z - 1)) * (-↑z.im / ↑(Complex.abs z)) +
        -↑z.im / ↑(Complex.abs (z - 1)) * (↑z.re / ↑(Complex.abs z))) *
    (z / ↑(Complex.abs z))
      := by rw [← a_re]

lemma 𝕆_re {z : ℂ} (hz : z ∈ 𝕆) : (z.re : ℂ) ∈ 𝕆 := by
  let l := O4 z reAxis
  apply in_𝕆_if_eq (Isect reAxis l O4_not_parallel)
  · exact Isect_in_𝕆 reAxis_in_𝕆 (O4_in_𝕆 hz reAxis_in_𝕆)
  simp [Isect, reAxis, O1, line.vec, l, O4]

lemma 𝕆_real_mul_real {a b : ℂ} (ha_real : a.im = 0) (hb_real : b.im = 0) (ha : a ∈ 𝕆) (hz : b ∈ 𝕆) : a * b ∈ 𝕆 := by
  -- Add i to b, multiply by a, and take the real component
  apply in_𝕆_if_eq (a * (b + Complex.I)).re
  · apply 𝕆_re
    apply 𝕆_real_mul_cmpl ha_real ha
    · simp [hb_real]
    apply 𝕆_add hz i_in_𝕆
  simp [Complex.ext_iff, ha_real, hb_real]

lemma 𝕆_i_mul {z : ℂ} (hz : z ∈ 𝕆) : Complex.I * z ∈ 𝕆 := by
  -- W.l.o.g., suppose that z ≠ 0.
  by_cases hz_ne_zero : z = 0
  · simp [hz_ne_zero, zero_in_𝕆]

  -- rotate z by π/2 radians
  let l₁ := O1 z 0 hz_ne_zero
  have hl₁ : l₁ ∈ 𝕆.lines := O1_in_𝕆 hz zero_in_𝕆
  have hl₁_vec : l₁.vec = -z / Complex.abs z := by
    simp [l₁, O1, line.vec]

  let l₂ := O4 0 l₁
  have hl₂ : l₂ ∈ 𝕆.lines := O4_in_𝕆 zero_in_𝕆 hl₁
  have hl₂_vec : l₂.vec = Complex.I * (-z / Complex.abs z) := by
    simp [l₂, O4, line.vec, div_self vec_well_defined]
    simp [l₁, O1]
  have l₁_l₂_not_parallel : ¬AreParallel l₁ l₂ := by
    have : (Complex.abs z : ℂ) ≠ 0 := by norm_cast; exact (AbsoluteValue.ne_zero_iff Complex.abs).mpr hz_ne_zero
    simp [AreParallel, line.vec]
    rw [← line.vec, ← line.vec, hl₁_vec, hl₂_vec, ← neg_mul]
    have : -z / Complex.abs z ≠ 0 := by exact div_ne_zero (neg_ne_zero.mpr hz_ne_zero) this
    constructor
    all_goals by_contra h
    all_goals symm at h
    all_goals apply (mul_eq_right₀ this).mp at h
    all_goals simp [Complex.ext_iff] at h
  have Isect_l₁_l₂ : Isect l₁ l₂ l₁_l₂_not_parallel = 0 := by
    have : (Complex.abs z : ℂ) ≠ 0 := by norm_cast; exact (AbsoluteValue.ne_zero_iff Complex.abs).mpr hz_ne_zero
    simp [Isect, l₁, l₂, O1, O4, line.vec, div_self this]
    ring_nf
    field_simp
    have : (z.im : ℂ) ^ 2 + (z.re : ℂ) ^ 2 ≠ 0 := by
      norm_cast
      simp_rw [← Complex.sq_abs_sub_sq_im z, add_sub_assoc']
      simp [hz_ne_zero]
    simp_rw [div_sub_div_same, ← neg_add', ← mul_add, neg_div, mul_div_assoc, div_self this]
    simp

  let l₃ := O3 l₁ l₂ -- attention: Here, the paper by James King has an error
  have hl₃ : l₃ ∈ 𝕆.lines := O3_in_𝕆 hl₁ hl₂
  have hl₃_z₁ : l₃.z₁ = 0 := by
    simp [l₃, O3, l₁_l₂_not_parallel, Isect_l₁_l₂]
  have hl₃_z₂ : l₃.z₂ = (1 + Complex.I)*(-z / Complex.abs z) := by
    simp [l₃, O3, l₁_l₂_not_parallel, Isect_l₁_l₂, hl₁_vec, hl₂_vec, ← one_add_mul]

  apply in_𝕆_if_eq (E2 z l₃)
  · exact E2_in_𝕆 z l₃ hz hl₃
  simp [E2, hl₃_z₁, hl₃_z₂, line.vec, div_abs hz_ne_zero]
  simp [div_add_div_same, div_div, mul_div_assoc', neg_div']
  simp [← neg_mul, ← add_mul, ← mul_div, mul_assoc, ← div_div, div_abs hz_ne_zero]
  ring_nf
  simp only [inv_eq_one_div, div_pow, mul_div_assoc', div_div, div_mul_eq_mul_div]
  have two_times_sqr_two_eq_one : 2 / (Complex.abs (1 + Complex.I) : ℂ) ^ 2 = 1 := by
    simp [Complex.sq_abs_eq]
    norm_num
  symm
  calc
    _ = (1 + Complex.I) * z * (2 * ((z.re^2 + z.im^2) /
        (Complex.abs z) ^ 2) / (Complex.abs (1 + Complex.I)) ^ 2)
        - z
          := by ring
    _ = (1 + Complex.I) * z * (2 * ((Complex.abs z) ^ 2 /
        (Complex.abs z) ^ 2) / (Complex.abs (1 + Complex.I)) ^ 2)
        - z
          := by rw [Complex.sq_abs_eq]
    _ = (1 + Complex.I) * z * (2 /
        (Complex.abs (1 + Complex.I)) ^ 2)
        - z
          := by simp [div_abs, hz_ne_zero]
    _ = (1 + Complex.I) * z
        - z
          := by simp [two_times_sqr_two_eq_one]
    _ = Complex.I * z := by ring

lemma 𝕆_im {z : ℂ} (hz : z ∈ 𝕆) : (z.im : ℂ) ∈ 𝕆 := by
  let l := O4 z imAxis
  apply in_𝕆_if_eq (-(Complex.I * Isect imAxis l O4_not_parallel))
  · exact 𝕆_neg (𝕆_i_mul (Isect_in_𝕆 imAxis_in_𝕆 (O4_in_𝕆 hz imAxis_in_𝕆)))
  simp [Isect, l, O4, line.vec, imAxis, reAxis, O1, mul_comm, ← mul_assoc]

theorem 𝕆_mul {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ 𝕆) (hz₂ : z₂ ∈ 𝕆) : z₁ * z₂ ∈ 𝕆 := by
  -- We can write
  have : z₁ * z₂ = z₁.re * z₂.re - z₁.im * z₂.im + Complex.I * (z₁.re * z₂.im + z₁.im * z₂.re) := by simp [Complex.ext_iff]
  rw [this]
  -- Now, this is just a concatination of previous lemmata
  apply 𝕆_add
  · simp [sub_eq_add_neg]
    apply 𝕆_add
    · apply 𝕆_real_mul_real
      all_goals simp [Complex.ofReal_im, 𝕆_re hz₁, 𝕆_re hz₂]
    · apply 𝕆_neg
      apply 𝕆_real_mul_real
      all_goals simp [Complex.ofReal_im, 𝕆_im hz₁, 𝕆_im hz₂]
  apply 𝕆_i_mul
  apply 𝕆_add
  · apply 𝕆_real_mul_real
    all_goals simp [Complex.ofReal_im, 𝕆_re hz₁, 𝕆_im hz₂]
  · apply 𝕆_real_mul_real
    all_goals simp [Complex.ofReal_im, 𝕆_im hz₁, 𝕆_re hz₂]

lemma 𝕆_real_inv_cmpl {a z : ℂ} (ha_real : a.im = 0) (ha : (a:ℂ) ∈ 𝕆) (hz_not_real : z.im ≠ 0) (hz : z ∈ 𝕆) (ha_not_zero : a≠ 0) :  z/a ∈ 𝕆 := by
  --defining the lines from z to 0 and 1, not parallel which is why z not be real
  have ha_eq_re : a = (a.re :ℂ):= by simp [Complex.ext_iff,ha_real]
  have z_ne_zero: z ≠ 0 := by simp [Complex.ext_iff, hz_not_real]
  have z_abs_ne_zero : Complex.abs z ≠ 0 := by simp[sub_ne_zero_of_ne z_ne_zero]; push_neg; exact z_ne_zero;
  let l₁ := O1 0 z z_ne_zero.symm
  have l₁_in_𝕆 : l₁ ∈ 𝕆.lines := by exact O1_in_𝕆 zero_in_𝕆 hz
  have l₁_vec : l₁.vec = z/Complex.abs z := by simp[line.vec,l₁, O1]
  have z_ne_a : a≠ z := by simp[Complex.ext_iff];intro h;rw[ha_real, Eq.comm];push_neg; exact   hz_not_real;
  have z_a_abs_ne_zero : Complex.abs (z-a)≠ 0 := by simp [Eq.comm, z_ne_a]
  let l₂ := O1 a z z_ne_a
  have l₂_vec : l₂.vec = (z-a)/Complex.abs (z-a) := by simp[line.vec,l₂, O1]
  have l₂_in_𝕆 : l₂ ∈ 𝕆.lines := by exact O1_in_𝕆 ha hz
  have l₁_l₂_not_parallel : ¬AreParallel l₁ l₂ := by
    unfold AreParallel
    push_neg
    constructor
    · simp [l₁_vec, l₂_vec, Complex.ext_iff]
      · intro h
        by_contra h'
        simp_rw[ha_real] at h'
        have := mul_eq_mul_of_div_eq_div z.im (z.im-0) z_abs_ne_zero z_a_abs_ne_zero h'
        simp_rw[sub_zero] at this
        have := mul_left_cancel₀ hz_not_real this
        rw[this] at h
        have := mul_eq_mul_of_div_eq_div z.re (z.re-a.re) z_abs_ne_zero z_abs_ne_zero h
        have := mul_right_cancel₀ z_abs_ne_zero this
        have := Eq.symm this
        simp [sub_eq_iff_eq_add] at this
        rw[this] at ha_eq_re
        rw[ha_eq_re] at ha_not_zero
        contradiction
    · simp [l₁_vec, l₂_vec, Complex.ext_iff]
      · intro h
        by_contra h'
        rw[← neg_div] at h'
        have := mul_eq_mul_of_div_eq_div z.im (-(z.im-a.im)) z_abs_ne_zero z_a_abs_ne_zero h'
        simp_rw[neg_mul_comm, ha_real, sub_zero] at this
        have := mul_left_cancel₀ hz_not_real this
        rw[this, div_neg, neg_neg] at h
        have := mul_eq_mul_of_div_eq_div z.re (z.re-a.re) z_abs_ne_zero z_abs_ne_zero h
        have := mul_right_cancel₀ z_abs_ne_zero this
        have := Eq.symm this
        simp [sub_eq_iff_eq_add] at this
        rw[this] at ha_eq_re
        rw[ha_eq_re] at ha_not_zero
        contradiction
  --defining the line parallel to l₂ going through a
  let l₃ := E1 1 l₂
  have l₃_in_𝕆 : l₃ ∈ 𝕆.lines := by exact E1_in_𝕆 1 l₂ one_in_𝕆 l₂_in_𝕆
  --helps a  lot with the computations
  have l₃_vec : l₃.vec = (a-z)/Complex.abs (z-a) := by
    simp [l₃,line.vec, E1,l₂_vec,l₂,O1]
    norm_cast
    simp [div_self z_a_abs_ne_zero,← neg_div]
  have l₂_l₃_parallel : AreParallel l₂ l₃ := by
    exact (E1_in_𝕆'' 1 l₂ one_in_𝕆 l₂_in_𝕆).2.2
  have l₁_l₃_not_parallel : ¬AreParallel l₁ l₃ := by
    exact Not_parallel_if_parallel l₁ l₂ l₃ l₁_l₂_not_parallel l₂_l₃_parallel
  --define the intersection of l₁ l₃
  let z₂ := Isect l₁ l₃ l₁_l₃_not_parallel
  --z₂ should be a*z
  apply in_𝕆_if_eq z₂
  exact Isect_in_𝕆 l₁_in_𝕆 l₃_in_𝕆;
  simp_rw [z₂, Isect,l₃_vec,l₃,E1,l₁_vec,l₁,O1]
  simp [ha_real];norm_cast
  simp [div_mul_div_comm, div_add_div_same, sub_mul];norm_cast
  rw[mul_comm z.re z.im,sub_add_eq_add_sub, add_neg_cancel, zero_sub, div_mul, mul_div_cancel_of_imp]
  push_cast;
  have hz_not_real' : (z.im :ℂ)≠ 0 := by simp [hz_not_real]
  rw[div_mul_eq_mul_div, ← neg_div, neg_neg, div_div_div_cancel_right₀]
  · norm_cast;simp [mul_comm,← mul_div,div_mul_cancel_right₀ hz_not_real', ← ha_eq_re];ring_nf;
  · simp [];push_neg; exact z_ne_a.symm
  · by_contra h; push_neg at h; rw[h.1] at z_abs_ne_zero; contradiction

lemma 𝕆_real_inv_real {a b : ℂ} (ha_real : a.im = 0) (hb_real : b.im = 0) (ha : a ∈ 𝕆) (hb : b ∈ 𝕆) (hb_ne_zero : b ≠ 0) : a / b ∈ 𝕆 := by
  -- Add i to b, multiply by a, and take the real component
  apply in_𝕆_if_eq ((a + Complex.I) / b ).re
  · apply 𝕆_re
    apply 𝕆_real_inv_cmpl hb_real hb
    · simp [ha_real]
    · apply 𝕆_add ha i_in_𝕆
    · exact hb_ne_zero
  simp [Complex.ext_iff, ha_real, hb_real]
  constructor
  · simp [Complex.div_re,add_div];left;exact hb_real
  · simp [Complex.div_im, hb_real, ha_real]

theorem 𝕆_inv {z : ℂ} (hz : z ∈ 𝕆) : z⁻¹ ∈ 𝕆 := by
  -- W.l.o.g., suppose that z ≠ 0.
  by_cases hz_ne_zero : z = 0
  · simp [hz_ne_zero, zero_in_𝕆]
  · -- We can write
    rw[inv_eq_one_div]
    have : 1/z = (z.re - z.im*Complex.I)/(z.re*z.re+z.im*z.im) := by simp [Complex.ext_iff, Complex.normSq, Complex.div_re, Complex.div_im,← neg_mul, mul_div_assoc, ← div_eq_mul_inv];
    rw [this]
    by_cases hz_not_real : z.im = 0
    · rw[hz_not_real]
      simp
      rw[inv_eq_one_div]
      apply 𝕆_real_inv_real rfl rfl one_in_𝕆 (𝕆_re hz)
      · simp [Complex.ext_iff] at hz_ne_zero
        by_contra h
        push_neg at hz_ne_zero
        apply hz_ne_zero
        exact Complex.ofReal_eq_zero.mp h
        · exact hz_not_real
    -- Now, this is just a concatination of previous lemmata
    apply 𝕆_real_inv_cmpl
    · simp [Complex.ofReal_im]
    · apply 𝕆_add
      · exact 𝕆_mul (𝕆_re hz) (𝕆_re hz)
      · exact 𝕆_mul (𝕆_im hz) (𝕆_im hz)
    · simp [hz_not_real]
    · rw [ sub_eq_add_neg]
      apply 𝕆_add (𝕆_re hz)
      apply 𝕆_neg
      apply 𝕆_mul (𝕆_im hz) (i_in_𝕆)
    · have := Complex.normSq_pos.mpr hz_ne_zero
      rw [Complex.normSq_apply] at this
      norm_cast
      exact ne_of_gt this

end mul


-- **Here comes the theorem stating that 𝕆 is a field.**

noncomputable def 𝕆Field : Subfield ℂ where
  carrier := 𝕆
  mul_mem' := 𝕆_mul
  one_mem' := one_in_𝕆
  add_mem' := 𝕆_add
  zero_mem' := zero_in_𝕆
  neg_mem' := 𝕆_neg
  inv_mem' := by
    intro z
    exact 𝕆_inv

theorem 𝕆_isField : IsField 𝕆Field := by
  exact Field.toIsField 𝕆Field


-- *ℚ ⊆ 𝕆*

lemma 𝕆_sub {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ 𝕆) (hz₂ : z₂ ∈ 𝕆) : z₁ - z₂ ∈ 𝕆 := by
  rw [sub_eq_add_neg]
  exact 𝕆_add hz₁ (𝕆_neg hz₂)

lemma 𝕆_div {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ 𝕆) (hz₂ : z₂ ∈ 𝕆) : z₁/z₂ ∈ 𝕆 := by
  rw [← mul_one z₁, mul_div_assoc, ← inv_eq_one_div]
  exact 𝕆_mul hz₁ (𝕆_inv hz₂)

lemma nat_in_𝕆 : ∀ n : ℕ, (n : ℂ) ∈ 𝕆 := by
  intro n
  induction n with
  | zero => norm_cast; exact zero_in_𝕆
  | succ n hn => push_cast; exact 𝕆_add hn one_in_𝕆

lemma int_in_𝕆 : ∀ n : ℤ, (n : ℂ) ∈ 𝕆 := by
  intro n
  induction n with
  | ofNat n => exact nat_in_𝕆 n
  | negSucc n => simp; rw [← neg_add]; apply 𝕆_neg; norm_cast; exact nat_in_𝕆 (1+n)

theorem rat_in_𝕆 : ∀ r : ℚ, (r : ℂ) ∈ 𝕆 := by
  intro r
  have : (r : ℂ) = r.num / r.den := by norm_cast; symm; exact Rat.divInt_self r
  simp_rw [this]
  apply 𝕆_div
  · apply int_in_𝕆
  · apply nat_in_𝕆

theorem Rat_subset_𝕆 : Set.range Complex.instRatCast.ratCast ⊆ 𝕆 := by
  intro z
  simp
  intro q hqz
  rw [← hqz]
  have : RatCast.ratCast q = (q : ℂ) := by rfl
  exact rat_in_𝕆 q


-- **𝕆 is closed under taking square and cube roots**

section square_root
lemma 𝕆_square_roots_pos_real {a : ℝ} {ha_pos : a > 0} (ha : (a : ℂ) ∈ 𝕆) :
    (√a : ℂ) ∈ 𝕆 := by
  let z₁ := Complex.I * (a - 1) / 2
  have hz₁ : z₁ ∈ 𝕆 := by
    apply 𝕆_div
    · exact 𝕆_mul i_in_𝕆 (𝕆_sub ha one_in_𝕆)
    apply nat_in_𝕆
  have hz₁_ne_neg_i : z₁ ≠ -Complex.I := by
    simp [z₁, Complex.ext_iff]
    simp [div_eq_iff, sub_eq_iff_eq_add]
    norm_num
    linarith

  -- O5 is returning a set of lines, not just one single line.
  -- Take the following line l out of O5
  let l : line := ⟨Complex.I*(a-1)/2, (√a-Complex.I)/2, (by simp [Complex.ext_iff]; intro h; linarith)⟩
  have hl_in_O5 : l ∈ O5 (-Complex.I) z₁ hz₁_ne_neg_i.symm reAxis := by
    simp [O5, reAxis, O1, z₁, l]
    constructor
    · use 1-√a
      simp only [Complex.ofReal_sub, Complex.ofReal_one, sub_sub_cancel, mul_div_assoc', ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀, sub_add_cancel]
    · ring_nf
      simp [Complex.abs, Complex.normSq]
      simp_rw [← Real.sqrt_mul (le_of_lt ha_pos), Real.sqrt_mul_self (le_of_lt ha_pos)]
      refine (Real.sqrt_inj ?_ ?_).mpr ?_
      · rw [← sq]
        apply add_nonneg
        · linarith
        · simp [sq_nonneg]
      · simp [← sq, sq_nonneg]
      ring_nf
  have hl : l ∈ 𝕆.lines := by
    apply O5_in_𝕆 (𝕆_neg i_in_𝕆) hz₁ reAxis_in_𝕆
    exact hl_in_O5

  -- The searched point z₂ is E2 of -i and l
  let z₂ := E2 (-Complex.I) l
  have hz₂ : z₂ ∈ 𝕆 := by
    exact E2_in_𝕆 (-Complex.I) l (𝕆_neg i_in_𝕆) hl

  -- We want to show that √a = z₂
  apply in_𝕆_if_eq z₂ hz₂
  simp [z₂, E2, l, line.vec]
  simp [Complex.ext_iff]
  have h1 : (Complex.abs (√a * (1 / 2) + Complex.I * (a * (-1 / 2))))⁻¹ ^ 2 = 4 / (a + a ^ 2) := by
    simp [mul_div_assoc', add_div',
      div_mul_cancel₀, map_div₀, div_pow,
      div_mul_eq_mul_div, Complex.sq_abs_eq_in_ℝ, Real.sq_sqrt (le_of_lt ha_pos)]
    norm_num
  have h2 : (a + a^2)/(a + a^2) = 1 := by
    simp (disch := field_simp_discharge) only [div_self, mul_one]
  constructor
  · simp [Complex.div_im, mul_div_assoc]
    ring_nf
    simp_rw [mul_assoc, mul_comm a, mul_comm (a^2), ← mul_add, h1]
    symm
    calc
      _ = √a * ((a + a ^ 2) / (a + a ^ 2)) := by ring
      _ = √a := by simp [h2]
  · simp [Complex.div_im, mul_div_assoc]
    ring_nf
    simp_rw [mul_assoc, mul_comm (a^2), mul_comm (a^3), add_assoc, ← mul_add, h1]
    symm
    calc
      _ = a - a * ((a + a ^ 2) / (a + a ^ 2)) := by ring
      _ = 0 := by simp [h2]

lemma 𝕆_abs {z : ℂ} (hz : z ∈ 𝕆) : (Complex.abs z : ℂ) ∈ 𝕆 := by
  simp [Complex.abs, Complex.normSq]
  by_cases h : z.re*z.re + z.im*z.im = 0
  · simp [h, zero_in_𝕆]
  apply 𝕆_square_roots_pos_real
  · simp_rw [lt_iff_le_and_ne]
    constructor
    · ring_nf
      exact add_nonneg (sq_nonneg z.re) (sq_nonneg z.im)
    · symm; exact h
  · push_cast
    apply 𝕆_add (𝕆_mul (𝕆_re hz) (𝕆_re hz)) (𝕆_mul (𝕆_im hz) (𝕆_im hz))

lemma vec_in_𝕆 {l : line} (hl : l ∈ 𝕆.lines) : l.vec ∈ 𝕆 := by
  -- w.l.o.g. l.vec ≠ ±i
  by_cases vec_ne_i : l.vec = Complex.I; · simp [vec_ne_i, i_in_𝕆]
  by_cases vec_ne_neg_i : l.vec = -Complex.I; · simp [vec_ne_neg_i, 𝕆_neg i_in_𝕆]

  -- w.l.o.g. l (now called l₁) passes through 0
  let l₁ := E1 0 l
  have hl₁ : l₁ ∈ 𝕆.lines := E1_in_𝕆 0 l zero_in_𝕆 hl
  have hl₁_z₁ : l₁.z₁ = 0 := by
    simp [l₁, E1]
  have : -l₁.vec = l.vec := by
    simp [l₁, E1, line.vec, div_self vec_well_defined]
  rw [← this] at vec_ne_i vec_ne_neg_i ⊢

  let l₂ := O4 1 l₁
  have hl₂ : l₂ ∈ 𝕆.lines := O4_in_𝕆 one_in_𝕆 hl₁
  have hl₂_z₁ : l₂.z₁ = 1 := by
    simp_rw [l₂, O4]
  have hl₂_z₂ : l₂.z₂ = 1 + Complex.I * l₁.vec := by
    simp_rw [l₂, O4]
  have hl₂_vec : l₂.vec = Complex.I * l₁.vec := by
    simp [line.vec, hl₂_z₁, hl₂_z₂]
    rw [div_self]; simp
    simp [l₁.z₁_ne_z₂.symm]

  let z₁ := Isect l₁ l₂ O4_not_parallel
  have hz₁ : z₁ ∈ 𝕆 := Isect_in_𝕆 hl₁ hl₂

  by_cases hcases : l₁.vec.re / |l₁.vec.re| = -1
  · -- if l₁.vec.re < 0
    apply in_𝕆_if_eq (z₁ / Complex.abs z₁) -- here it's the positive version
    · exact 𝕆_div hz₁ (𝕆_abs hz₁)
    simp [z₁, Isect, hl₂_vec, hl₂_z₁, hl₁_z₁, vec_abs_one]
    have : (l₁.vec.im * l₁.vec.im + l₁.vec.re * l₁.vec.re : ℂ) = 1 := by
      simp [add_comm, ← sq, ← Complex.sq_abs_eq, vec_abs_one]
    simp [this]
    rw [neg_eq_iff_eq_neg, ← neg_div, ← neg_mul, mul_comm, mul_div_assoc, eq_comm, mul_right_eq_self₀]
    simp [vec_ne_zero, neg_div, neg_eq_iff_eq_neg]
    norm_cast; norm_num
    exact hcases
  · -- if l₁.vec.re > 0
    have hcases : l₁.vec.re / |l₁.vec.re| = 1 := by
      have : l₁.vec.re ≠ 0 := by
        intro l₁_vec_re_eq_zero
        simp [Complex.ext_iff, l₁_vec_re_eq_zero, neg_eq_iff_eq_neg] at vec_ne_i vec_ne_neg_i
        have : Complex.abs l₁.vec = 1 := vec_abs_one l₁
        simp [Complex.abs, Complex.normSq, l₁_vec_re_eq_zero, ← sq, vec_ne_i, vec_ne_neg_i] at this
      rw [← neg_eq_iff_eq_neg, ← neg_div] at hcases
      simp [div_eq_one_iff_eq, this] at hcases ⊢
      rw [eq_comm, abs_eq_self]
      simp [eq_comm, abs_eq_neg_self] at hcases
      exact le_of_lt hcases
    apply in_𝕆_if_eq (-z₁ / Complex.abs z₁) -- and here the negative version
    · exact 𝕆_div (𝕆_neg hz₁) (𝕆_abs hz₁)
    simp [z₁, Isect, hl₂_vec, hl₂_z₁, hl₁_z₁, vec_abs_one]
    have : (l₁.vec.im * l₁.vec.im + l₁.vec.re * l₁.vec.re : ℂ) = 1 := by
      simp [add_comm, ← sq, ← Complex.sq_abs_eq, vec_abs_one]
    simp [this]
    rw [← mul_neg, mul_comm, mul_div_assoc, eq_comm, mul_right_eq_self₀]
    simp [vec_ne_zero]
    norm_cast

lemma half_angle {z : ℂ} (hz : z ∈ 𝕆) : Complex.exp (z.arg/2 * Complex.I) ∈ 𝕆 := by
  -- w.l.o.g. z ≠ 0 and z.im ≠ 0
  by_cases z_ne_zero : z = 0
  · simp [z_ne_zero, one_in_𝕆]
  by_cases z_im_ne_zero : (z.im : ℂ) = 0
  · have : z.arg = 0 ∨ z.arg = Real.pi := by
      norm_cast at z_im_ne_zero
      simp [Complex.arg, z_im_ne_zero, Real.pi_ne_zero, Real.pi_ne_zero.symm, le_or_lt]
    rcases this with h|h
    · simp [h, one_in_𝕆]
    · simp [h, Complex.exp_mul_I, i_in_𝕆]

  apply in_𝕆_if_eq ((Complex.abs z + z) / Complex.abs (Complex.abs z + z))
  · have := 𝕆_add (𝕆_abs hz) hz
    exact 𝕆_div this (𝕆_abs this)
  · -- Prove that -l₂.vec = (Complex.abs z + z) / Complex.abs (Complex.abs z + z)
    -- is equal to Complex.exp (z.arg/2 * Complex.I)
    norm_cast
    simp [Complex.ext_iff, Complex.exp_re, Complex.exp_im]
    constructor
    · -- the real part, i.e. cos (z.arg / 2) = (Complex.abs z + z.re) / Complex.abs (↑(Complex.abs z) + z)
      rw [Real.cos_half (le_of_lt (Complex.arg_mem_Ioc z).1) (Complex.arg_mem_Ioc z).2]
      rw [Real.sqrt_eq_iff_mul_self_eq]
      · simp_rw [Complex.cos_arg z_ne_zero, div_mul_div_comm, Complex.mul_self_abs, Complex.abs_apply, Complex.normSq_apply]
        simp
        ring_nf
        rw [Real.sq_sqrt (add_nonneg (sq_nonneg z.re) (sq_nonneg z.im))]
        field_simp
        have : z.re * 2 / (√(z.re ^ 2 + z.im ^ 2) * 2) = z.re / √(z.re ^ 2 + z.im ^ 2) := by
          simp [mul_comm, ← div_div]
        rw [this, add_assoc (z.re * √(z.re ^ 2 + z.im ^ 2) * 2) (z.re^2) (z.im^2)]
        simp_rw [sq, ← Complex.normSq_apply z, ← Complex.abs_apply, ← Complex.sq_abs z]
        rw [add_assoc (z.re * Complex.abs z * 2) (Complex.abs z ^2), ← mul_two]
        rw [← add_mul, mul_div_assoc, mul_comm (z.re * Complex.abs z + Complex.abs z ^2), ← div_div, div_self two_ne_zero, mul_div, mul_one]
        rw [eq_div_iff]
        · rw [sq, ← add_mul, ← mul_comm (Complex.abs z), ← mul_assoc]
          simp [one_add_div, z_ne_zero]
          ring_nf
        · simp [sq, ← add_mul, z_ne_zero]
          rw [add_eq_zero_iff_eq_neg', Complex.abs_eq_sqrt_sq_add_sq]
          norm_cast at z_im_ne_zero
          simp [Real.sqrt_eq_cases, ← sq, z_im_ne_zero]
          simp [← Complex.sq_abs_eq_in_ℝ]
      · have := (Real.cos_mem_Icc z.arg).1
        linarith
      · simp [div_nonneg_iff]
        left
        rw [Complex.abs_apply, Complex.normSq_apply, ← neg_le_iff_add_nonneg]
        apply Real.le_sqrt_of_sq_le
        simp [← sq, sq_nonneg]
    · -- the imaginary part, i.e. sin (z.arg / 2) = z.im / Complex.abs ((Complex.abs z) + z)
      have : (1 - Real.cos z.arg) / 2 = z.im / Complex.abs ((Complex.abs z) + z) * (z.im / Complex.abs ((Complex.abs z) + z)) := by
        simp_rw [Complex.cos_arg z_ne_zero, div_mul_div_comm, Complex.mul_self_abs, Complex.abs_apply, Complex.normSq_apply]
        simp
        ring_nf
        rw [Real.sq_sqrt (add_nonneg (sq_nonneg z.re) (sq_nonneg z.im))]
        field_simp
        rw [neg_div, ← sub_eq_add_neg]
        have : z.re * 2 / (√(z.re ^ 2 + z.im ^ 2) * 2) = z.re / √(z.re ^ 2 + z.im ^ 2) := by
          simp [mul_comm, ← div_div]
        rw [this, add_assoc (z.re * √(z.re ^ 2 + z.im ^ 2) * 2) (z.re^2) (z.im^2)]
        simp_rw [sq, ← Complex.normSq_apply z, ← Complex.abs_apply, ← Complex.sq_abs z]
        rw [add_assoc (z.re * Complex.abs z * 2) (Complex.abs z ^2), ← mul_two]
        rw [← add_mul, mul_div_assoc, mul_comm (z.re * Complex.abs z + Complex.abs z ^2), ← div_div, div_self two_ne_zero, mul_div, mul_one]
        rw [eq_div_iff]
        · rw [sq, ← add_mul, ← mul_comm (Complex.abs z), ← mul_assoc]
          simp [one_sub_div, z_ne_zero]
          ring_nf
          exact Complex.sq_abs_sub_sq_re z
        · simp [sq, ← add_mul, z_ne_zero]
          rw [add_eq_zero_iff_eq_neg', Complex.abs_eq_sqrt_sq_add_sq]
          norm_cast at z_im_ne_zero
          simp [Real.sqrt_eq_cases, ← sq, z_im_ne_zero]
          simp [← Complex.sq_abs_eq_in_ℝ]
      by_cases z_arg_sign : 0 ≤ z.arg
      · -- case 0 ≤ z.arg (or equivalently, 0 ≤ z.im)
        rw [Real.sin_half_eq_sqrt z_arg_sign]
        · rw [Real.sqrt_eq_iff_mul_self_eq]
          · exact this
          · have := (Real.cos_mem_Icc z.arg).2
            linarith
          · simp [div_nonneg_iff, Complex.arg_nonneg_iff.mp z_arg_sign]
        · have := (Complex.arg_mem_Ioc z).2
          linarith
      · -- case z.arg < 0 (or equivalently, z.im < 0)
        rw [not_le] at z_arg_sign
        rw [Real.sin_half_eq_neg_sqrt, neg_eq_iff_eq_neg]
        · rw [Real.sqrt_eq_iff_mul_self_eq]
          · rw [neg_mul_neg]
            exact this
          · have := (Real.cos_mem_Icc z.arg).2
            linarith
          · simp at z_arg_sign
            simp [div_nonpos_iff, le_of_lt z_arg_sign]
        · have := (Complex.arg_mem_Ioc z).1
          linarith
        · exact le_of_lt z_arg_sign

theorem 𝕆_square_roots {z : ℂ} (hz : z ∈ 𝕆) : ∃ z' ∈ 𝕆, z = z'^2 := by
  use √(Complex.abs z) * Complex.exp (z.arg / 2 * Complex.I)
  constructor
  · apply 𝕆_mul
    · by_cases h : Complex.abs z = 0
      · simp [h, zero_in_𝕆]
      · apply 𝕆_square_roots_pos_real
        · simp [(AbsoluteValue.ne_zero_iff Complex.abs).mp h, AbsoluteValue.nonneg Complex.abs z]
        · exact 𝕆_abs hz
    · exact half_angle hz
  · ring_nf
    norm_cast
    rw [Real.sq_sqrt (AbsoluteValue.nonneg Complex.abs z)]
    rw [← Complex.exp_nat_mul (z.arg * Complex.I * (1/2)) 2]
    simp [← mul_assoc, mul_comm]
    rw [mul_comm, mul_comm Complex.I]
    exact Eq.symm (Complex.abs_mul_exp_arg_mul_I z)

end square_root


section cube_root

lemma slope_in_𝕆 {l : line} (hl : l ∈ 𝕆.lines) : (l.vec.im / l.vec.re : ℂ) ∈ 𝕆 := by
  apply 𝕆_div
  · exact 𝕆_im (vec_in_𝕆 hl)
  · exact 𝕆_re (vec_in_𝕆 hl)

lemma 𝕆_depressed_cubics (p q : ℝ) (hp : (p : ℂ) ∈ 𝕆) (hq : (q : ℂ) ∈ 𝕆) :
    ∀ m : ℝ, (m : ℂ) ∈ (⟨1,0,p,q⟩ : Cubic ℂ).roots → (m : ℂ) ∈ 𝕆 := by
  -- m is a zero of the depressed cubic polynomial x^3 + p*x + q
  intro m hm
  simp [Cubic.roots, Cubic.toPoly] at hm
  obtain ⟨poly_nonneg, hm⟩ := hm

  -- w.l.o.g. m ≠ 0
  by_cases m_ne_zero : m = 0
  · rw [m_ne_zero]; exact zero_in_𝕆

  -- w.l.o.g. m^3 + m ≠ 0
  by_cases m_cubed_plus_m_ne_zero : Complex.I = q+p*Complex.I
  · simp [Complex.ext_iff] at m_cubed_plus_m_ne_zero
    simp [← m_cubed_plus_m_ne_zero, pow_three, ← mul_add_one] at hm
    rcases hm with hm|hm
    · rw [hm]; exact zero_in_𝕆
    · rw [← sq, add_eq_zero_iff_eq_neg, ← Complex.I_sq, sq_eq_sq_iff_eq_or_eq_neg] at hm
      simp [Complex.ext_iff] at hm

  -- From m^3+pm+q=0 and m≠0 follows directly:
  have hm' : p + q/m = -m*m := by
    have hm : m * (p + q/m + m*m) = 0 := by
      ring_nf at hm ⊢
      rw [← mul_comm q, mul_inv_cancel_right₀ m_ne_zero]
      norm_cast at hm
      rw [add_assoc, ← add_comm q, ← add_assoc] at hm
      exact hm
    simp [mul_eq_zero, m_ne_zero] at hm
    rw [neg_mul, ← add_eq_zero_iff_eq_neg, hm]

  -- Define two lines l₁
  let l₁ := O1 (-Complex.I) (1-Complex.I) (by simp [Complex.ext_iff])
  have hl₁ : l₁ ∈ 𝕆.lines := O1_in_𝕆 (𝕆_neg i_in_𝕆) (𝕆_sub one_in_𝕆 i_in_𝕆)
  have hl₁_vec : l₁.vec = 1 := by simp [l₁, O1, line.vec]

  -- and l₂
  let l₂ := O1 (-q) (-q+Complex.I) (by simp [Complex.ext_iff])
  have hl₂ : l₂ ∈ 𝕆.lines := O1_in_𝕆 (𝕆_neg hq) (𝕆_add (𝕆_neg hq) i_in_𝕆)
  have hl₂_z₁ : l₂.z₁ = -q := by simp [l₂, O1]
  have hl₂_vec : l₂.vec = Complex.I := by simp [l₂, O1, line.vec]

  -- which, used O6 on them, give us a line l₃ with slope m
  let l₃ : line := {
    z₁ := (p+q/m)*Complex.I
    z₂ := 1+(m+p+q/m)*Complex.I
    z₁_ne_z₂ := by simp [Complex.ext_iff]
  }
  have hl₃_vec : l₃.vec = (1 + m*Complex.I) / Complex.abs (1 + m*Complex.I) := by
    simp [l₃, line.vec, add_assoc, add_mul, ← add_assoc]
  have : l₃ ∈ O6 Complex.I (q+p*Complex.I) m_cubed_plus_m_ne_zero l₁ l₂ := by
    rw [O6, Set.mem_setOf_eq, ← and_assoc]
    constructor
    · simp [hl₃_vec, hl₁_vec, hl₂_vec, Complex.ext_iff]
    constructor
    · use 2*m + m*m*Complex.I
      simp [dist_point_line, hl₁_vec, Complex.ext_iff]
      rw [add_assoc, hm', neg_mul, ← sub_eq_add_neg]
      constructor
      · -- 2m + m^2*i lies in l₃.points ...
        use 1-2*m
        ring_nf
        trivial
      · simp [l₁, O1]
        constructor
        · -- ... and on the parabola induced by the directrix l₁ and the focal point i
          simp [Complex.abs_apply, Complex.normSq_apply]
          rw [← neg_add', neg_mul_neg, Real.sqrt_mul_self (add_nonneg zero_le_one (mul_self_nonneg m))]
          rw [Real.sqrt_eq_iff_mul_self_eq_of_pos]
          · ring_nf
          · have : m*m ≥ 0 := by exact (mul_self_nonneg m)
            linarith
        · -- 2m + m^2*i is the only point having the properties above
          intro z t htz_re htz_im h
          rw [← Complex.re_add_im z, add_sub_assoc, ← sub_one_mul] at h
          simp [← htz_re, ← htz_im] at h ⊢
          simp [Complex.abs_apply, Complex.normSq_apply] at h
          rw [Real.sqrt_eq_iff_mul_self_eq, Real.mul_self_sqrt] at h
          · rw [← sub_eq_zero] at h
            ring_nf at h ⊢
            have h : t = 1 - 2*m := by
              rw [← sub_eq_zero, ← sq_eq_zero_iff, ← h]
              ring_nf
            simp [h]
            ring_nf
            trivial
          · apply mul_self_nonneg
          · simp [add_nonneg, mul_self_nonneg]
          · apply Real.sqrt_nonneg
    · use q/(m*m) + (q/m-m*m) * Complex.I
      have hm'' : p = -(q/m + m*m) := by
        simp [neg_add, ← neg_mul, ← hm']
      simp [dist_point_line, hl₂_vec, hl₂_z₁, Complex.ext_iff, hm'']
      norm_cast
      simp
      constructor
      · -- q/(m^2) + (q/m - m^2)*i lies in l₃.points ...
        use 1 - q/(m*m)
        ring_nf
        simp [sq, mul_assoc, m_ne_zero]
      · ring_nf
        constructor
        · -- ... and on the parabola induced by the directrix l₂ and the focal point (q+p*i)
          simp_rw [Complex.abs_apply, Complex.normSq_apply, ← sq]
          norm_cast; simp
          norm_cast; simp
          rw [Real.sqrt_sq_eq_abs, Real.sqrt_eq_iff_mul_self_eq, abs_mul_abs_self]
          · simp [sq]
            ring_nf
          · simp [add_nonneg, sq_nonneg]
          · exact abs_nonneg (-q - q * (m ^ 2)⁻¹)
        · -- q/(m^2) + (q/m - m^2)*i is the only point having the properties above
          intro z t htz_re htz_im h
          rw [← Complex.re_add_im z] at h
          simp [← htz_re, ← htz_im] at h ⊢
          simp [Complex.abs_apply, Complex.normSq_apply] at h
          norm_cast at h; simp at h
          simp_rw [← sq, Real.sqrt_sq_eq_abs] at h
          rw [Real.sqrt_eq_iff_mul_self_eq, abs_mul_abs_self] at h
          · rw [← sub_eq_zero] at h
            ring_nf at h
            simp [m_ne_zero] at h
            ring_nf at h ⊢
            have h : t = 1 - q/(m*m) := by
              rw [← sub_eq_zero, ← sq_eq_zero_iff, ← zero_mul (1/m^2), ← h, ← sub_eq_zero]
              ring_nf
              simp [m_ne_zero]
              ring_nf
            simp [h]
            ring_nf
            simp [sq, mul_assoc, m_ne_zero]
          · simp [add_nonneg, sq_nonneg]
          · apply abs_nonneg

  have hl₃ : l₃ ∈ 𝕆.lines := by
    apply O6_in_𝕆 i_in_𝕆 (𝕆_add hq (𝕆_mul hp i_in_𝕆)) hl₁ hl₂
    exact this

  apply in_𝕆_if_eq (l₃.vec.im / l₃.vec.re)
  · apply 𝕆_div
    · apply 𝕆_im
      · apply vec_in_𝕆 hl₃
    · apply 𝕆_re
      · apply vec_in_𝕆 hl₃

  -- Left to show: m = ↑l₃.vec.im / ↑l₃.vec.re
  simp [hl₃_vec, Complex.ext_iff]

lemma 𝕆_cubics (a b c : ℝ) (ha : (a : ℂ) ∈ 𝕆) (hb : (b : ℂ) ∈ 𝕆) (hc : (c : ℂ) ∈ 𝕆) :
    ∀ (m : ℝ), (m : ℂ) ∈ (⟨1,a,b,c⟩ : Cubic ℂ).roots → (m : ℂ) ∈ 𝕆 := by
  -- m is a zero of the cubic polynomial x^3 + a*x^2 + b*x + c
  intro m hm
  simp [Cubic.roots, Cubic.toPoly] at hm
  obtain ⟨poly_nonneg, hm⟩ := hm

  -- Change of variables (t is the variable of the future depressed version t^3 + p*t + q)
  -- let t := x + a/3

  let p := (3*b - a^2)/3
  have hp : (p : ℂ) ∈ 𝕆 := by
    simp [p, sq]
    apply 𝕆_div
    · apply 𝕆_sub
      · apply 𝕆_mul
        · apply nat_in_𝕆
        · exact hb
      · exact 𝕆_mul ha ha
    · apply nat_in_𝕆

  let q := (2*a^3 - 9*a*b + 27*c)/27
  have hq : (q : ℂ) ∈ 𝕆 := by
    simp [q, pow_three]
    apply 𝕆_div
    · apply 𝕆_add
      · apply 𝕆_sub
        · apply 𝕆_mul
          · apply nat_in_𝕆
          · exact 𝕆_mul ha (𝕆_mul ha ha)
        · apply 𝕆_mul
          · apply 𝕆_mul
            · apply nat_in_𝕆
            · exact ha
          · exact hb
      · apply 𝕆_mul
        · apply nat_in_𝕆
        · exact hc
    · apply nat_in_𝕆

  let depr_poly := (⟨1,0,p,q⟩ : Cubic ℂ)

  -- This depressed cubic has a root m' with
  let m' := m + a/3
  have : (m' : ℂ) ∈ depr_poly.roots := by
    simp [depr_poly, Cubic.roots, Cubic.toPoly, p, q]
    constructor
    · simp [Polynomial.ext_iff]
      use 3
      simp [Polynomial.coeff]
    · norm_cast at hm ⊢
      ring_nf
      calc
       _ = m ^ 3 + a * m ^ 2 + b * m + c := by ring_nf
       _ = 0 := by exact hm
  -- since m' is a root of a depressed cubic, it lies in 𝕆
  have : (m' : ℂ) ∈ 𝕆 := by
    apply 𝕆_depressed_cubics p q hp hq
    exact this
  -- m and m' differ only by numbers in 𝕆 and operations which are closed in 𝕆.
  rw [← add_zero m, ← sub_self (a/3), ← add_sub_assoc]
  push_cast
  apply 𝕆_sub (by norm_cast)
  apply 𝕆_div ha
  apply nat_in_𝕆

lemma 𝕆_cube_roots_real {a : ℝ} (ha : (a : ℂ) ∈ 𝕆) :
    ∃ (x : ℝ), (x : ℂ) ∈ 𝕆 ∧ x^3 = a := by
  have cubic := 𝕆_cubics 0 0 (-a) zero_in_𝕆 zero_in_𝕆 (by simp [𝕆_neg ha])
  simp [Cubic.roots, Cubic.toPoly] at cubic
  have : Polynomial.X ^ 3 + -Polynomial.C (a : ℂ) ≠ 0 := by
    simp [← sub_eq_add_neg, sub_eq_zero, Polynomial.ext_iff]
    use 3
    simp

  by_cases a_nonneg : a ≥ 0
  · specialize cubic (a^((1 : ℝ)/3)) this
    norm_cast at cubic
    have : (a ^ ((1 : ℝ) / 3)) ^ 3 = a := by
      simp
      exact Real.rpow_inv_natCast_pow a_nonneg (by trivial)
    rw [this] at cubic
    simp at cubic

    use (a^((1 : ℝ)/3))
    rw [this]
    simp [cubic]
  · have neg_a_nonneg : -a ≥ 0 := by linarith
    specialize cubic (-(-a)^((1 : ℝ)/3)) this
    norm_cast at cubic
    have : (-(-a) ^ ((1 : ℝ) / 3)) ^ 3 = a := by
      rw [neg_pow]
      norm_num
      simp [neg_eq_iff_eq_neg]
      exact Real.rpow_inv_natCast_pow neg_a_nonneg (by trivial)
    rw [this] at cubic
    simp at cubic

    use (-(-a)^((1 : ℝ)/3))
    rw [this]
    simp [cubic]

lemma trisect_angle {z : ℂ} (hz : z ∈ 𝕆) : Complex.exp (z.arg/3 * Complex.I) ∈ 𝕆 := by
  -- w.l.o.g. z ≠ 0 and z.im ≠ 0
  by_cases z_ne_zero : z = 0
  · simp [z_ne_zero, one_in_𝕆]
  by_cases z_im_ne_zero : (z.im : ℂ)  = 0
  · have : z.arg = 0 ∨ z.arg = Real.pi := by
      norm_cast at z_im_ne_zero
      simp [Complex.arg, z_im_ne_zero, Real.pi_ne_zero, Real.pi_ne_zero.symm, le_or_lt]
    rcases this with h|h
    · simp [h, one_in_𝕆]
    · rw [h, Complex.exp_mul_I]
      norm_cast
      simp [Real.cos_pi_div_three, Real.sin_pi_div_three, mul_comm]
      apply 𝕆_add
      · exact 𝕆_inv (by apply nat_in_𝕆)
      · apply 𝕆_i_mul
        apply 𝕆_div
        · apply 𝕆_square_roots_pos_real (by apply nat_in_𝕆)
          norm_num
        · apply nat_in_𝕆

  apply in_𝕆_if_eq ((2 * Complex.abs z + z) / Complex.abs (2 * Complex.abs z + z))
  · have := 𝕆_add (𝕆_double (𝕆_abs hz)) hz
    exact 𝕆_div this (𝕆_abs this)
  · -- Prove that -l₂.vec = (Complex.abs z + z) / Complex.abs (Complex.abs z + z)
    -- is equal to Complex.exp (z.arg/2 * Complex.I)
    norm_cast
    #check Complex.sin_three_mul
    -- maybe Complex.ext_iff instead of Complex.ext_abs_arg_iff
    -- Yes, do it!!!!
    -- Just like in sqrt version!!!!
    rw [Complex.ext_abs_arg_iff, Complex.abs_exp_ofReal_mul_I]
    constructor
    · simp; symm; apply div_self
      norm_cast at z_im_ne_zero
      simp [Complex.ext_iff, z_im_ne_zero]
    · rw [Complex.exp_mul_I, Complex.arg_cos_add_sin_mul_I]
      · norm_cast at z_im_ne_zero
        simp
        rw [div_eq_mul_inv (2 * Complex.abs z + z), Complex.arg_mul, Complex.arg_inv]
        · simp [Complex.arg_ofReal_of_nonneg, Real.pi_ne_zero.symm]
          -- Prove that z.arg/2 = (Complex.abs z + z).arg
          /-simp [Complex.arg]
          by_cases z_re_nonneg : 0 ≤ z.re
          · have : 0 ≤ Complex.abs z + z.re := add_nonneg (AbsoluteValue.nonneg Complex.abs z) z_re_nonneg
            simp [z_re_nonneg, this]
            sorry
          · sorry-/
          sorry
        · simp [Complex.ext_iff, z_im_ne_zero]
        · simp [Complex.ext_iff, z_im_ne_zero]
        · simp [Complex.arg_inv, Complex.arg_ofReal_of_nonneg, Real.pi_ne_zero.symm]
          exact Complex.arg_mem_Ioc (2 * Complex.abs z + z)
      · simp
        have := Real.pi_pos
        constructor
        · have := (Complex.arg_mem_Ioc z).1
          linarith
        · have := (Complex.arg_mem_Ioc z).2
          linarith

theorem 𝕆_cube_roots {z : ℂ} (hz : z ∈ 𝕆) : ∃ z' ∈ 𝕆, z = z'^3 := by
  obtain ⟨r,hr,hr_cubed_eq_abs⟩ := 𝕆_cube_roots_real (𝕆_abs hz)
  use r * Complex.exp (z.arg / 3 * Complex.I)
  constructor
  · apply 𝕆_mul hr (trisect_angle hz)
  · ring_nf
    norm_cast
    rw [hr_cubed_eq_abs]
    rw [← Complex.exp_nat_mul (z.arg * Complex.I * (1/3)) 3]
    simp [← mul_assoc, mul_comm]
    rw [mul_comm, mul_comm Complex.I]
    exact Eq.symm (Complex.abs_mul_exp_arg_mul_I z)

end cube_root
