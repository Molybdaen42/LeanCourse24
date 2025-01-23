import LeanCourse.Project.defs
import LeanCourse.Project.lemmata_for_O
open Classical
open Construction
open ComplexConjugate

section E1

noncomputable def E1 (z : ℂ) (l : line) : line :=
  ⟨z,z - l.vec,(by simp [sub_eq_neg_add, vec_ne_zero l])⟩

/-- Given a point z and a line l, fold a line parallel to l that goes through z.-/
lemma E1_in_𝕆 (z : ℂ) (l : line) (hz : z ∈ 𝕆) (hl : l ∈ 𝕆.lines) :
  E1 z l ∈ 𝕆.lines := by
    unfold E1
    apply in_𝕆_lines_if_eqq (O4 z (O4 z l))
    · exact O4_in_𝕆 hz (O4_in_𝕆 hz hl)
    · -- show that the built line is equal to O4 z (O4 z l)
      simp [O4, line.vec]
      simp [mul_div_assoc', div_div_eq_mul_div, div_mul_eq_mul_div, div_div]
      simp [mul_div_assoc, sub_eq_add_neg, ← mul_assoc, ← neg_div, neg_sub]
      rfl

/-- Given a point z and a line l, fold a line parallel to l that goes through z.-/
lemma E1_in_𝕆' (z : ℂ) (l : line) (hz : z ∈ 𝕆) (hl : l ∈ 𝕆.lines) :
  ∃ l' ∈ 𝕆.lines, l'.z₁ = z ∧ l'.z₂ = z - l.vec := by
    use ⟨z,z - l.vec,(by simp [sub_eq_neg_add, vec_ne_zero l])⟩
    constructor
    · exact E1_in_𝕆 z l hz hl
    · simp

lemma E1_parallel_l (z : ℂ) (l : line):
  AreParallel l (E1 z l):= by
    unfold E1
    unfold AreParallel
    unfold line.vec
    simp
    right
    simp_rw [neg_div', neg_neg]
    rw[← line.vec, div_self]
    rw[div_one]
    have := l.z₁_ne_z₂
    simp
    exact this.symm

end E1
section E2
variable (z : ℂ) (l : line)

/-- Given a point z and a line l, reflect z across l.-/
-- 2 * (l.z₁ + ⟨z-l.z₁,l.vect⟩ * l.vec) - z
-- = 2 * (l.z₁ + ((z-l.z₁)*conj l.vec).re * l.vec) - z
noncomputable def E2 : ℂ :=
  2 * (l.z₁ + ((z-l.z₁) * conj l.vec).re * l.vec) - z

lemma O4_not_parallel_to_E1 :
  ¬AreParallel (O4 z l) (E1 z l) := by
    simp [AreParallel, line.vec]
    simp [E1, O4]
    constructor
    · rw [← one_mul (-l.vec / (Complex.abs l.vec)),neg_div, mul_neg, ← neg_mul, mul_div_assoc]
      by_contra h
      have := mul_eq_mul_right_iff.mp h
      simp [vec_ne_zero] at this
      simp [Complex.ext_iff] at this
    · rw [← one_mul (-l.vec / (Complex.abs l.vec)),neg_div, mul_neg, neg_neg, mul_div_assoc]
      by_contra h
      have := mul_eq_mul_right_iff.mp h
      simp [vec_ne_zero] at this
      simp [Complex.ext_iff] at this

lemma O3_on_O4_and_E1 :
  (O3 (O4 z l) (E1 z l)).z₁ = z ∧
  (O3 (O4 z l) (E1 z l)).z₂ = z + Complex.I * l.vec - l.vec ∧
  (O3 (O4 z l) (E1 z l)).vec = (Complex.I - 1) * l.vec / Complex.abs (Complex.I - 1) := by
    rw [← and_assoc]
    constructor
    · simp [O3, O4_not_parallel_to_E1 z l]
      simp [O4, E1, Isect]
      simp [line.vec, div_self vec_well_defined]
      rfl
    · simp [O3, O4_not_parallel_to_E1 z l]
      simp_rw [line.vec]
      simp [O4, E1, Isect, vec_abs_one, add_sub_right_comm]
      simp [← sub_eq_add_neg, ← sub_one_mul, vec_abs_one]
      simp_rw [line.vec]

lemma l_not_parallel_to_O3_on_O4_and_E1 :
  ¬AreParallel l (O3 (O4 z l) (E1 z l)) := by
    simp [AreParallel]
    rw [line.vec, line.vec, (O3_on_O4_and_E1 z l).1, (O3_on_O4_and_E1 z l).2.1, ← line.vec]
    ring_nf; simp only [inv_eq_one_div, mul_div_assoc', mul_one, neg_div', div_add_div_same]
    -- use some ring properties on h
    rw [← neg_neg (-(Complex.I*l.vec)+l.vec), neg_add, neg_neg, ← sub_eq_add_neg]
    rw [mul_div_assoc, ← sub_one_mul, ← sub_one_mul, mul_div, mul_comm]
    -- |x * y| = |x| * |y| and |l.vec| = 1
    simp [vec_abs_one]
    constructor
    · by_contra h
      -- Devide out l.vec
      symm at h
      rw [mul_div_assoc, (mul_eq_left₀ (vec_ne_zero l))] at h
      -- Find the contradiction
      simp [Complex.ext_iff] at h
    · -- the same above, just with an extra minus sign
      by_contra h
      -- Devide out l.vec
      symm at h
      rw [← neg_mul, mul_div_assoc, neg_mul_comm, (mul_eq_left₀ (vec_ne_zero l))] at h
      -- Find the contradiction
      simp [Complex.ext_iff] at h

lemma O4_not_parallel_to_O4_on_O3_on_O4_and_E1 :
  ¬AreParallel (O4 z l) (O4 (Isect l (O3 (O4 z l) (E1 z l)) (l_not_parallel_to_O3_on_O4_and_E1 z l)) (O3 (O4 z l) (E1 z l))) := by
    have := (O3_on_O4_and_E1 z l)
    simp_rw [AreParallel, O4, line.vec] at *
    simp_rw [this, O3]
    simp [O4_not_parallel_to_E1 z l]
    rw [← line.vec]
    simp only [div_div_eq_mul_div, add_sub_assoc, add_sub_cancel_left, mul_div_assoc', div_mul_eq_mul_div, div_div, neg_div']
    simp [← sub_one_mul, vec_abs_one]
    rw [← neg_mul, neg_mul_comm]
    rw [mul_comm (Complex.I-1) l.vec, ← mul_assoc]
    simp_rw [mul_div_assoc, mul_assoc (Complex.I*l.vec)]
    simp [div_self, vec_ne_zero l]
    field_simp [Complex.ext_iff]

lemma O4_on_z₁_and_l₄ :
  (O4 (Isect l (O3 (O4 z l) (E1 z l)) (l_not_parallel_to_O3_on_O4_and_E1 z l)) (O3 (O4 z l) (E1 z l))).vec
   = -(Complex.I + 1) * l.vec / Complex.abs (Complex.I - 1) := by
    have := (O3_on_O4_and_E1 z l)
    simp_rw [O4, line.vec, Isect] at *
    simp_rw [this, O3]
    simp [O4_not_parallel_to_E1 z l]
    rw [← line.vec]
    simp [O4, E1, Isect, vec_abs_one, add_sub_right_comm]
    simp [add_comm, ← sub_eq_add_neg, ← sub_one_mul, vec_abs_one]
    have : (Complex.abs (Complex.I - 1) : ℂ) ≠ 0 := by simp [Complex.ext_iff]
    simp [div_self this]
    simp [neg_add_eq_sub, Complex.ext_iff, ← neg_div, neg_add_eq_sub]

lemma E2_in_𝕆 (hz : z ∈ 𝕆) (hl : l ∈ 𝕆.lines) :
  E2 z l ∈ 𝕆 := by
    -- l₁ is perpendicular to l and passes through z.
    let l₁ := O4 z l
    have hl₁ : l₁ ∈ 𝕆.lines := O4_in_𝕆 hz hl
    have hl₁_vec: l₁.vec = Complex.I * (l.vec) := by
      simp[l₁, O4, line.vec, div_self vec_well_defined]

    -- l₂ is parallel to l and passes through z.
    let l₂ := E1 z l
    have hl₂ : l₂ ∈ 𝕆.lines := E1_in_𝕆 z l hz hl
    have hl₁_l₂_not_parallel : ¬AreParallel l₁ l₂ := O4_not_parallel_to_E1 z l

    -- l₃ bisects the angle between l₁ and l₂. The three of them intersect in z.
    let l₃ := O3 l₁ l₂
    have hl₃ : l₃ ∈ 𝕆.lines := O3_in_𝕆 hl₁ hl₂
    have hl₃_z₁ : l₃.z₁ = z := (O3_on_O4_and_E1 z l).1
    have hl₃_z₂ : l₃.z₂ = z + Complex.I * l.vec - l.vec := (O3_on_O4_and_E1 z l).2.1
    have hl₃_vec : l₃.vec = (Complex.I - 1) * l.vec / Complex.abs (Complex.I - 1) := (O3_on_O4_and_E1 z l).2.2
    have hl_l₃_not_parallel : ¬AreParallel l l₃ := l_not_parallel_to_O3_on_O4_and_E1 z l

    -- z₁ is the intersection of l and l₃.
    let z₁ := Isect l l₃ hl_l₃_not_parallel
    have hz₁ : z₁ ∈ 𝕆 := Isect_in_𝕆 hl hl₃

    -- l₄ is orthogonal to l₃ and goes through z₁.
    let l₄ := O4 z₁ l₃
    have hl₄ : l₄ ∈ 𝕆.lines := O4_in_𝕆 hz₁ hl₃
    have hl₁_l₄_not_parallel : ¬AreParallel l₁ l₄ := O4_not_parallel_to_O4_on_O3_on_O4_and_E1 z l
    have hl₄_vec : l₄.vec = -(Complex.I + 1) * l.vec / Complex.abs (Complex.I - 1) :=
      O4_on_z₁_and_l₄ z l

    -- The result is the intersection of l₁ and l₄.
    apply in_𝕆_if_eq (Isect l₁ l₄ hl₁_l₄_not_parallel)
    · exact Isect_in_𝕆 hl₁ hl₄
    · simp_rw [E2, Isect, hl₄_vec, l₄, O4, z₁, Isect, hl₃_vec, hl₃_z₁, hl₁_vec, l₁, O4]
      norm_cast
      simp [div_mul_eq_mul_div, div_div_eq_mul_div, div_div, neg_div']
      simp_rw [← neg_mul, neg_add, neg_sub, sub_neg_eq_add, neg_neg, ← sub_eq_add_neg]

      -- In there, there are multiple |l.vec|^2 = 1 hidden as l.vec.im^2 + l.vec.re^2 (more or less)
      have : (l.vec.im + l.vec.re) * l.vec.im + (l.vec.re - l.vec.im) * l.vec.re = 1 := by
        ring_nf
        simp [← Complex.sq_abs_sub_sq_im, vec_abs_one]
      norm_cast; simp [this]
      have : (l.vec.im + l.vec.re) * l.vec.im + (-l.vec.im + l.vec.re) * l.vec.re = 1 := by
        ring_nf
        simp [← Complex.sq_abs_sub_sq_im, vec_abs_one]
      norm_cast; simp [this]

      -- Again, delete those squares
      have : (Complex.abs (Complex.I - 1) : ℂ) ≠ 0 := by simp [Complex.ext_iff]
      simp_rw [mul_assoc, mul_comm (Complex.abs (Complex.I - 1) : ℂ), neg_div, mul_div_assoc, div_self this]
      norm_cast
      ring_nf
      have : l.vec.re ^ 3 = l.vec.re ^ 2 * l.vec.re := by ring
      norm_cast; simp [this, ← Complex.sq_abs_sub_sq_im, vec_abs_one]
      simp [Complex.ext_iff]
      ring_nf
      norm_cast; simp [this, ← Complex.sq_abs_sub_sq_im, vec_abs_one]
      ring_nf
      trivial

lemma E2_ne_z (h : z ∉ l.points) : z ≠ E2 z l := by
  simp [E2]
  by_contra h'
  let k : ℝ := ((z.re - l.z₁.re) * l.vec.re + (z.im - l.z₁.im) * l.vec.im)
  have h' : z = 2 * (l.z₁ + k * l.vec) - z := by simp [k]; exact h'
  simp [sub_eq_add_neg] at h'
  have h' := add_eq_of_eq_add_neg h'
  simp [← two_mul] at h'
  by_cases hk : k ≠ 0
  · have := line_eq_if_add_vec l hk
    simp_rw [← h', line_eq_iff_both_points_lie_in_the_other'] at this
    have := this.2
    contradiction
  · simp at hk
    simp [hk] at h'
    rw [h'] at h
    have := z₁_on_l l
    contradiction

/-lemma O2_on_E2' (z : ℂ) (l : line) (hz : z ∈ 𝕆) (hl : l ∈ 𝕆.lines) (h : z ∉ l.points) :
  (O2 z (E2 z l hz hl) (E2_ne_z h)).eq l := by
    simp_rw [line_eq_iff_both_points_lie_in_the_other']
    simp [E2, O2]
    constructor
    · use 1 - (l.z₁-(l.z₁+((z.re-l.z₁.re)*l.vec.re+(z.im-l.z₁.im)*l.vec.im)*l.vec)) / (Complex.I*(2*(l.z₁+((z.re-l.z₁.re)*l.vec.re+(z.im-l.z₁.im)*l.vec.im)*l.vec)-2*z))
      sorry
    · sorry
-/
end E2
