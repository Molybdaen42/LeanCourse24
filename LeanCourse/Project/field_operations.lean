import LeanCourse.Project.defs
import LeanCourse.Project.lemmata_for_O
import LeanCourse.Project.important_lines_and_points_in_O
import LeanCourse.Project.two_folding_lemmata
open Classical
open Construction
open ComplexConjugate

-- **Addition**
section add

/-- 𝕆 is closed under negation.-/
theorem 𝕆_neg {z : ℂ} (hz : z ∈ 𝕆) : -z ∈ 𝕆 := by
  -- W.l.o.g. z ≠ 0
  by_cases z_ne_zero : z = 0
  · simp [z_ne_zero]; exact 𝕆_zero

  -- Idea: Mirror z across the perpendicular line sitting at 0.
  let l₁ := O1 z 0 z_ne_zero
  have hl₁ : l₁ ∈ 𝕆.lines := O1_in_𝕆 hz 𝕆_zero

  let l₂ := O4 0 l₁
  have hl₂ : l₂ ∈ 𝕆.lines := O4_in_𝕆 𝕆_zero hl₁
  have hl₂_z₁ : l₂.z₁ = 0 := by simp [l₂, O4]
  have hl₂_z₂ : l₂.z₂ = -Complex.I * z / Complex.abs z := by
    simp [l₂, O4, line.vec, l₁, O1]
    ring
  have hl₂_vec : l₂.vec = -Complex.I * z / Complex.abs z := by
    simp [line.vec, hl₂_z₁, hl₂_z₂, div_abs z_ne_zero, neg_div]

  apply in_𝕆_if_eq (E2 z l₂)
  · exact 𝕆_E2 z l₂ hz hl₂
  simp [E2, hl₂_z₁, hl₂_vec]
  ring_nf

/-- We can double numbers in 𝕆.-/
lemma 𝕆_double {z : ℂ} (hz : z ∈ 𝕆) : 2 * z ∈ 𝕆 := by
  -- W.l.o.g. z ≠ 0
  by_cases z_ne_zero : z = 0
  · simp [z_ne_zero]; exact 𝕆_zero

  -- Idea: Mirror the 0 across the perpendicular line sitting at z.
  let l₁ := O1 z 0 z_ne_zero
  have hl₁ : l₁ ∈ 𝕆.lines := O1_in_𝕆 hz 𝕆_zero

  let l₂ := O4 z l₁
  have hl₂ : l₂ ∈ 𝕆.lines := O4_in_𝕆 hz hl₁
  have hl₂_z₁ : l₂.z₁ = z := by simp [l₂, O4]
  have hl₂_z₂ : l₂.z₂ = z - Complex.I * z / Complex.abs z := by
    simp [l₂, O4, line.vec, l₁, O1]
    ring
  have hl₂_vec : l₂.vec = -Complex.I * z / Complex.abs z := by
    simp [line.vec, hl₂_z₁, hl₂_z₂, div_abs z_ne_zero, neg_div]

  apply in_𝕆_if_eq (E2 0 l₂)
  · exact 𝕆_E2 0 l₂ 𝕆_zero hl₂
  simp [E2, hl₂_z₁, hl₂_vec, z_ne_zero]
  ring_nf

/-- We can add two numbers z₁, z₂ ∈ 𝕆 that are multiples of each other.-/
lemma 𝕆_add_multiples {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ 𝕆) (hz₂ : z₂ ∈ 𝕆) (h_multiple : ∃ a : ℝ, z₁ = a * z₂) : z₁ + z₂ ∈ 𝕆 := by
  obtain ⟨a,ha⟩ := h_multiple
  -- Here is the proof why we can assume w.l.o.g. that |z₁| < |z₂| holds.
  by_cases h_abs_ne : z₁ = z₂ ∨ z₁ = -z₂
  · -- The case that z₁ = ±z₂,
    -- therefore their sum equals 0 or 2 * z₁. Apply 𝕆_zero or 𝕆_double.

    simp [ha] at h_abs_ne
    rcases h_abs_ne with a_one|a_neg_one
    · -- a = 1
      simp [ha, a_one, ← two_mul]
      exact 𝕆_double hz₂
    · -- a = -1
      simp [ha, a_neg_one, ← two_mul]
      exact 𝕆_zero
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
    have hl₁ : l₁ ∈ 𝕆.lines := O1_in_𝕆 hz₁ 𝕆_zero

    -- Next, we fold z₂ onto z₁ using O2.
    let l₂ := O2 z₁ z₂ hz₁_ne_z₂
    have hl₂ : l₂ ∈ 𝕆.lines := O2_in_𝕆 hz₁ hz₂

    -- Now, let's mirror 0 across l₂ and get z₁+z₂
    apply in_𝕆_if_eq (E2 0 l₂)
    · exact 𝕆_E2 0 l₂ 𝕆_zero hl₂
    simp [E2, l₂, O2, line.vec, ha]
    ring_nf

/-- 𝕆 is closed under addition.-/
theorem 𝕆_add {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ 𝕆) (hz₂ : z₂ ∈ 𝕆) : z₁ + z₂ ∈ 𝕆 := by
  -- Wlog we can assume that z₁ and z₂ are not equal to 0 or to a multiple (by a real number) of each other
  by_cases hz₁_ne_zero : z₁ = 0; simp [hz₁_ne_zero, hz₂]
  by_cases hz₂_ne_zero : z₂ = 0; simp [hz₂_ne_zero, hz₁]
  by_cases hz₁_ne_real_mult_z₂ : ∃ a : ℝ, z₁ = a * z₂
  · exact 𝕆_add_multiples hz₁ hz₂ hz₁_ne_real_mult_z₂
  push_neg at hz₁_ne_zero hz₂_ne_zero hz₁_ne_real_mult_z₂

  -- First step: create two lines from 0 to z₁ resp. z₂.
  let l₁ := O1 0 z₁ hz₁_ne_zero.symm
  let l₂ := O1 0 z₂ hz₂_ne_zero.symm
  have hl₁ : l₁ ∈ 𝕆.lines := O1_in_𝕆 𝕆_zero hz₁
  have hl₂ : l₂ ∈ 𝕆.lines := O1_in_𝕆 𝕆_zero hz₂

  -- Second step: fold a line parallel to l₁ that goes through z₂
  -- and a line parallel to l₂ that goes through z₁.
  let l₃ := E1 z₂ l₁
  let l₄ := E1 z₁ l₂
  have hl₃ : l₃ ∈ 𝕆.lines := 𝕆_E1 z₂ l₁ hz₂ hl₁
  have hl₄ : l₄ ∈ 𝕆.lines := 𝕆_E1 z₁ l₂ hz₁ hl₂
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

/-- 𝕆 is closed under subtraction.-/
lemma 𝕆_sub {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ 𝕆) (hz₂ : z₂ ∈ 𝕆) : z₁ - z₂ ∈ 𝕆 := by
  rw [sub_eq_add_neg]
  exact 𝕆_add hz₁ (𝕆_neg hz₂)


end add
-- **Muliplication**
section mul

/-- We can multiply a real with a complex number.-/
lemma 𝕆_real_mul_cmpl {a z : ℂ} (ha_real : a.im = 0) (ha : (a:ℂ) ∈ 𝕆) (hz_not_real : z.im ≠ 0) (hz : z ∈ 𝕆) : a * z ∈ 𝕆 := by
  --defining the lines from z to 0 and 1, not parallel which is why z not be real
  have z_ne_zero: z ≠ 0 := by simp [Complex.ext_iff, hz_not_real]
  have z_abs_ne_zero : Complex.abs z ≠ 0 := by simp[sub_ne_zero_of_ne z_ne_zero]; push_neg; exact z_ne_zero;
  let l₁ := O1 0 z z_ne_zero.symm
  have l₁_in_𝕆 : l₁ ∈ 𝕆.lines := by exact O1_in_𝕆 𝕆_zero hz
  have l₁_vec : l₁.vec = z/Complex.abs z := by simp[line.vec,l₁, O1]
  have z_ne_one: z ≠ 1 := by simp [Complex.ext_iff, hz_not_real]
  have z_abs_ne_one : Complex.abs (z-1) ≠ 0 := by simp[sub_ne_zero_of_ne z_ne_zero]; push_neg; exact z_ne_one;
  let l₂ := O1 1 z z_ne_one.symm
  have l₂_vec : l₂.vec = (z-1)/Complex.abs (z-1) := by simp[line.vec,l₂, O1]
  have l₂_in_𝕆 : l₂ ∈ 𝕆.lines := by exact O1_in_𝕆 𝕆_one hz
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
  have l₃_in_𝕆 : l₃ ∈ 𝕆.lines := by exact 𝕆_E1 a l₂ ha l₂_in_𝕆
  --helps a  lot with the computations
  have : Complex.abs (z-1) ≠ 0 := by simp[sub_ne_zero_of_ne z_ne_one]; push_neg; exact z_ne_one;
  have l₃_vec : l₃.vec = (1-z)/Complex.abs (z-1) := by
    simp [l₃,line.vec, E1,l₂, O1]
    norm_cast
    simp [div_self this,← neg_div]
  have l₂_l₃_parallel : AreParallel l₂ l₃ := by
    exact (E1_parallel_l a l₂)
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

/-- The real part of any z ∈ 𝕆 lies in 𝕆.-/
lemma 𝕆_re {z : ℂ} (hz : z ∈ 𝕆) : (z.re : ℂ) ∈ 𝕆 := by
  let l := O4 z reAxis
  apply in_𝕆_if_eq (Isect reAxis l O4_not_parallel)
  · exact Isect_in_𝕆 𝕆_reAxis (O4_in_𝕆 hz 𝕆_reAxis)
  simp [Isect, reAxis, O1, line.vec, l, O4]

/-- We can multiply two real numbers.-/
lemma 𝕆_real_mul_real {a b : ℂ} (ha_real : a.im = 0) (hb_real : b.im = 0) (ha : a ∈ 𝕆) (hz : b ∈ 𝕆) : a * b ∈ 𝕆 := by
  -- Add i to b, multiply by a, and take the real component
  apply in_𝕆_if_eq (a * (b + Complex.I)).re
  · apply 𝕆_re
    apply 𝕆_real_mul_cmpl ha_real ha
    · simp [hb_real]
    apply 𝕆_add hz 𝕆_i
  simp [Complex.ext_iff, ha_real, hb_real]

/-- We can multiply with i, i.e. rotate by π/2 radians.-/
lemma 𝕆_i_mul {z : ℂ} (hz : z ∈ 𝕆) : Complex.I * z ∈ 𝕆 := by
  -- W.l.o.g., suppose that z ≠ 0.
  by_cases hz_ne_zero : z = 0
  · simp [hz_ne_zero, 𝕆_zero]

  -- Draw the line going through 0 and z.
  let l₁ := O1 z 0 hz_ne_zero
  have hl₁ : l₁ ∈ 𝕆.lines := O1_in_𝕆 hz 𝕆_zero
  have hl₁_vec : l₁.vec = -z / Complex.abs z := by
    simp [l₁, O1, line.vec]

  -- Rotate the line by π/2 radians.
  let l₂ := O4 0 l₁
  have hl₂ : l₂ ∈ 𝕆.lines := O4_in_𝕆 𝕆_zero hl₁
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

  -- Take the diagonal between l₁ and l₂ ...
  let l₃ := O3 l₁ l₂ -- Attention: Here, the paper by James King has an error
  have hl₃ : l₃ ∈ 𝕆.lines := O3_in_𝕆 hl₁ hl₂
  have hl₃_z₁ : l₃.z₁ = 0 := by
    simp [l₃, O3, l₁_l₂_not_parallel, Isect_l₁_l₂]
  have hl₃_z₂ : l₃.z₂ = (1 + Complex.I)*(-z / Complex.abs z) := by
    simp [l₃, O3, l₁_l₂_not_parallel, Isect_l₁_l₂, hl₁_vec, hl₂_vec, ← one_add_mul]

  -- ... such that we can mirror z across it.
  apply in_𝕆_if_eq (E2 z l₃)
  · exact 𝕆_E2 z l₃ hz hl₃
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

/-- The real part of any z ∈ 𝕆 lies in 𝕆.-/
lemma 𝕆_im {z : ℂ} (hz : z ∈ 𝕆) : (z.im : ℂ) ∈ 𝕆 := by
  let l := O4 z imAxis
  apply in_𝕆_if_eq (-(Complex.I * Isect imAxis l O4_not_parallel))
  · exact 𝕆_neg (𝕆_i_mul (Isect_in_𝕆 𝕆_imAxis (O4_in_𝕆 hz 𝕆_imAxis)))
  simp [Isect, l, O4, line.vec, imAxis, reAxis, O1, mul_comm, ← mul_assoc]

/-- 𝕆 is closed under multiplication.-/
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

lemma 𝕆_pow_nat {z : ℂ} {n : ℕ} (hz : z ∈ 𝕆) : z^n ∈ 𝕆 := by
  induction n with
  | zero => simp; exact 𝕆_one
  | succ n hn => simp [pow_add]; exact 𝕆_mul hn hz

end mul
section div

/-- We can take the division of z ∈ 𝕆 \ ℝ by a ∈ 𝕆 ∩ ℝ.-/
lemma 𝕆_cmpl_div_real {a z : ℂ} (ha_real : a.im = 0) (ha : (a:ℂ) ∈ 𝕆) (hz_not_real : z.im ≠ 0) (hz : z ∈ 𝕆) (ha_not_zero : a≠ 0) :  z/a ∈ 𝕆 := by
  --defining the lines from z to 0 and 1, not parallel which is why z not be real
  have ha_eq_re : a = (a.re :ℂ):= by simp [Complex.ext_iff,ha_real]
  have z_ne_zero: z ≠ 0 := by simp [Complex.ext_iff, hz_not_real]
  have z_abs_ne_zero : Complex.abs z ≠ 0 := by simp[sub_ne_zero_of_ne z_ne_zero]; push_neg; exact z_ne_zero;
  let l₁ := O1 0 z z_ne_zero.symm
  have l₁_in_𝕆 : l₁ ∈ 𝕆.lines := by exact O1_in_𝕆 𝕆_zero hz
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
  have l₃_in_𝕆 : l₃ ∈ 𝕆.lines := by exact 𝕆_E1 1 l₂ 𝕆_one l₂_in_𝕆
  --helps a  lot with the computations
  have l₃_vec : l₃.vec = (a-z)/Complex.abs (z-a) := by
    simp [l₃,line.vec, E1,l₂_vec,l₂,O1]
    norm_cast
    simp [div_self z_a_abs_ne_zero,← neg_div]
  have l₂_l₃_parallel : AreParallel l₂ l₃ := by
    exact (E1_parallel_l 1 l₂ )
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

/-- We can take the division of two real numbers.-/
lemma 𝕆_real_div_real {a b : ℂ} (ha_real : a.im = 0) (hb_real : b.im = 0) (ha : a ∈ 𝕆) (hb : b ∈ 𝕆) (hb_ne_zero : b ≠ 0) : a / b ∈ 𝕆 := by
  -- Add i to b, multiply by a, and take the real component
  apply in_𝕆_if_eq ((a + Complex.I) / b ).re
  · apply 𝕆_re
    apply 𝕆_cmpl_div_real hb_real hb
    · simp [ha_real]
    · apply 𝕆_add ha 𝕆_i
    · exact hb_ne_zero
  simp [Complex.ext_iff, ha_real, hb_real]
  constructor
  · simp [Complex.div_re,add_div];left;exact hb_real
  · simp [Complex.div_im, hb_real, ha_real]

/-- We can take the inverse of a number.-/
theorem 𝕆_inv {z : ℂ} (hz : z ∈ 𝕆) : z⁻¹ ∈ 𝕆 := by
  -- W.l.o.g., suppose that z ≠ 0.
  by_cases hz_ne_zero : z = 0
  · simp [hz_ne_zero, 𝕆_zero]
  · -- We can write
    rw[inv_eq_one_div]
    have : 1/z = (z.re - z.im*Complex.I)/(z.re*z.re+z.im*z.im) := by simp [Complex.ext_iff, Complex.normSq, Complex.div_re, Complex.div_im,← neg_mul, mul_div_assoc, ← div_eq_mul_inv];
    rw [this]
    by_cases hz_not_real : z.im = 0
    · rw[hz_not_real]
      simp
      rw[inv_eq_one_div]
      apply 𝕆_real_div_real rfl rfl 𝕆_one (𝕆_re hz)
      · simp [Complex.ext_iff] at hz_ne_zero
        by_contra h
        push_neg at hz_ne_zero
        apply hz_ne_zero
        exact Complex.ofReal_eq_zero.mp h
        · exact hz_not_real
    -- Now, this is just a concatination of previous lemmata
    apply 𝕆_cmpl_div_real
    · simp [Complex.ofReal_im]
    · apply 𝕆_add
      · exact 𝕆_mul (𝕆_re hz) (𝕆_re hz)
      · exact 𝕆_mul (𝕆_im hz) (𝕆_im hz)
    · simp [hz_not_real]
    · rw [ sub_eq_add_neg]
      apply 𝕆_add (𝕆_re hz)
      apply 𝕆_neg
      apply 𝕆_mul (𝕆_im hz) (𝕆_i)
    · have := Complex.normSq_pos.mpr hz_ne_zero
      rw [Complex.normSq_apply] at this
      norm_cast
      exact ne_of_gt this

/-- 𝕆 is closed under division.-/
theorem 𝕆_div {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ 𝕆) (hz₂ : z₂ ∈ 𝕆) : z₁/z₂ ∈ 𝕆 := by
  rw [← mul_one z₁, mul_div_assoc, ← inv_eq_one_div]
  exact 𝕆_mul hz₁ (𝕆_inv hz₂)

lemma 𝕆_pow_int {z : ℂ} {n : ℤ} (hz : z ∈ 𝕆) : z^n ∈ 𝕆 := by
  induction n with
  | ofNat n => exact 𝕆_pow_nat hz
  | negSucc n => simp; rw [← inv_pow]; exact 𝕆_pow_nat (𝕆_inv hz)

end div
section Field_theorem
-- **Here comes the theorem stating that 𝕆 is a field.**

noncomputable def 𝕆Field : Subfield ℂ where
  carrier := 𝕆
  mul_mem' := 𝕆_mul
  one_mem' := 𝕆_one
  add_mem' := 𝕆_add
  zero_mem' := 𝕆_zero
  neg_mem' := 𝕆_neg
  inv_mem' := by
    intro z
    exact 𝕆_inv

theorem 𝕆_isField : IsField 𝕆Field := by
  exact Field.toIsField 𝕆Field


end Field_theorem
section Rational_numbers_are_in_𝕆
-- **The rational numbers ℚ are a subset of 𝕆**
-- It's also true that ℚ is a subfield of 𝕆, but we won't prove this.

/-- The natural numbers are constructible.-/
lemma 𝕆_nat {n : ℕ} : (n : ℂ) ∈ 𝕆 := by
  induction n with
  | zero => norm_cast; exact 𝕆_zero
  | succ n hn => push_cast; exact 𝕆_add hn 𝕆_one

/-- The integers are constructible.-/
lemma 𝕆_int {n : ℤ} : (n : ℂ) ∈ 𝕆 := by
  induction n with
  | ofNat n => exact 𝕆_nat
  | negSucc n => simp; rw [← neg_add]; apply 𝕆_neg; norm_cast; exact 𝕆_nat

/-- The rational numbers are constructible.-/
theorem 𝕆_rat {r : ℚ} : (r : ℂ) ∈ 𝕆 := by
  have : (r : ℂ) = r.num / r.den := by norm_cast; symm; exact Rat.divInt_self r
  simp_rw [this]
  apply 𝕆_div
  · apply 𝕆_int
  · apply 𝕆_nat

theorem 𝕆_rat' : Set.range Complex.instRatCast.ratCast ⊆ 𝕆 := by
  intro z
  simp
  intro q hqz
  rw [← hqz]
  have : RatCast.ratCast q = (q : ℂ) := by rfl
  exact 𝕆_rat
