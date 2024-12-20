import LeanCourse.Project.defs
import LeanCourse.Project.lemmata_for_O
open Classical
open Construction
open ComplexConjugate

/- **Field Operations** -/

lemma 𝕆_double {z : ℂ} (hz : z ∈ 𝕆) : 2 * z ∈ 𝕆 := by
  -- W.l.o.g. z ≠ 0
  by_cases hz_ne_zero : z = 0; simp [hz_ne_zero]; exact zero_in_𝕆

  -- Define the line through 0 and z.
  let l₁ := O1 z 0 hz_ne_zero
  have : l₁ ∈ 𝕆.lines := O1_in_𝕆 hz zero_in_𝕆
  -- Now define the line perpendicular to l₁ which goes through z.
  let l₂ := O4 z l₁
  have : l₂ ∈ 𝕆.lines := O4_in_𝕆 hz this
  -- After that, we mirror 0 across l₂ and get 2 * z.
  --have : h_two_z_in_𝕆 := E2 0 l₂ zero_in_𝕆 this

  -- Now is just left to show that the output of E2 equals 2 * z.
  sorry

/-- This is the main part of the proof of 𝕆_add_multiples. Here we suppose w.l.o.g. that |z₁| < |z₂|.-/
lemma _𝕆_add_multiples {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ 𝕆) (hz₂ : z₂ ∈ 𝕆) (h_multiple : ∃ a : ℝ, z₁ = a * z₂) (h_abs_ne : Complex.abs z₁ < Complex.abs z₂) : z₁ + z₂ ∈ 𝕆 := by
  /- -- ToDo: Want to do this without using the multiplication lemma
  -- in order to use addition in there
  obtain ⟨a,ha⟩ := h_multiple
  simp [ha, ← add_one_mul]
  norm_cast
  exact 𝕆_real_mult hz₂-/
  by_cases hz₁_ne_zero : z₁ = 0; simp [hz₁_ne_zero, hz₂]
  by_cases hz₂_ne_zero : z₂ = 0; simp [hz₂_ne_zero, hz₁]
  by_cases hz₁_ne_h₂ : z₁ = z₂; rw [← hz₁_ne_h₂,← two_mul]; apply 𝕆_double hz₁
  push_neg at hz₁_ne_zero hz₂_ne_zero
  obtain ⟨a,ha⟩ := h_multiple

  sorry
lemma 𝕆_add_multiples {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ 𝕆) (hz₂ : z₂ ∈ 𝕆) (h_multiple : ∃ a : ℝ, z₁ = a * z₂) : z₁ + z₂ ∈ 𝕆 := by
  -- Here is the proof why we can assume w.l.o.g. that |z₁| < |z₂| holds.
  by_cases h_cases : Complex.abs z₁ < Complex.abs z₂
  · exact _𝕆_add_multiples hz₁ hz₂ h_multiple h_cases
  · simp at h_cases
    by_cases h_abs_ne : Complex.abs z₁ = Complex.abs z₂;
    · -- The case that |z₁| = |z₂|. By h_multiple, we know that z₁ = ±z₂,
      -- therefore their sum equals 0 or 2 * z₁. Apply zero_in_𝕆 or 𝕆_double.
      sorry
    have h_cases : Complex.abs z₂ < Complex.abs z₁ := by
      exact lt_of_le_of_ne h_cases (fun a ↦ h_abs_ne (a.symm))
    rw [add_comm]
    obtain ⟨a,ha⟩ := h_multiple
    by_cases ha_ne_zero : a = 0; simp [ha_ne_zero, ha, hz₂]
    have h_multiple : ∃ a : ℝ, z₂ = a * z₁ := by
      use a⁻¹
      simp [ha, ha_ne_zero]
    exact _𝕆_add_multiples hz₂ hz₁ h_multiple h_cases

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

  -- Take the level of depth that z₁ and z₂ lie in 𝕆
  have hz₁_copy := hz₁
  have hz₂_copy := hz₂
  simp [𝕆] at hz₁_copy hz₂_copy ⊢
  obtain ⟨N₁,hz₁N⟩ := hz₁_copy
  obtain ⟨N₂,hz₂N⟩ := hz₂_copy
  let N := max N₁ N₂

  -- First step: create two lines from 0 to z₁ resp. z₂.
  let l₁ := O1 0 z₁ hz₁_ne_zero.symm
  let l₂ := O1 0 z₂ hz₂_ne_zero.symm

  -- Second step: fold a line parallel to l₁ that goes through z₂
  -- and a line parallel to l₂ that goes through z₁.
  let ⟨l₃,hl₃,hl₃_def⟩ := E1 z₂ l₁ hz₂ (O1_in_𝕆 zero_in_𝕆 hz₁)
  let ⟨l₄,hl₄,hl₄_def⟩ := E1 z₁ l₂ hz₁ (O1_in_𝕆 zero_in_𝕆 hz₂)

  have hl₃_l₄_not_parallel : ¬AreParallel l₃ l₄ := by
    simp [AreParallel, line.vec, hl₃_def, hl₄_def, l₁, l₂, O1, div_self, hz₁_ne_zero, hz₂_ne_zero]
    constructor
    · specialize hz₁_ne_real_mult_z₂ (Complex.abs z₁ / Complex.abs z₂)
      push_cast at hz₁_ne_real_mult_z₂
      simp [div_mul_comm] at hz₁_ne_real_mult_z₂
      calc
        z₁ / (Complex.abs z₁) ≠ z₂ / (Complex.abs z₂) * (Complex.abs z₁) / (Complex.abs z₁) := by

          sorry
        _ = z₂ / (Complex.abs z₂) := by simp [div_self, hz₁_ne_zero]
    · specialize hz₁_ne_real_mult_z₂ (-(Complex.abs z₁) / (Complex.abs z₂))
      push_cast at hz₁_ne_real_mult_z₂
      simp [div_mul_comm] at hz₁_ne_real_mult_z₂
      calc
        -(z₁ / (Complex.abs z₁)) ≠ z₂ / (Complex.abs z₂) * (Complex.abs z₁) / (Complex.abs z₁) := by
          sorry
        _ = z₂ / (Complex.abs z₂) := by simp [div_self, hz₁_ne_zero]

  -- Take the level of depth that l₃ and l₄ lie in 𝕆.points
  have hl₃_copy := hl₃
  have hl₄_copy := hl₄
  simp [𝕆.lines] at hl₃_copy hl₄_copy
  obtain ⟨N₁,hl₃N⟩ := hl₃_copy
  obtain ⟨N₂,hl₄N⟩ := hl₄_copy
  let N := max N₁ N₂

  -- Last step: take the intersectioon of l₃ and l₄.
  let z₃ := Isect l₃ l₄ hl₃_l₄_not_parallel

  -- tidying it up
  use N+1
  right
  simp [generate_points]
  use l₃
  constructor; apply 𝕆ₙ.lines_inc N₁ N (Nat.le_max_left N₁ N₂); exact hl₃N
  use l₄
  constructor; apply 𝕆ₙ.lines_inc N₂ N (Nat.le_max_right N₁ N₂); exact hl₄N
  use hl₃_l₄_not_parallel
  simp [Isect, line.vec, hl₃_def.1, hl₃_def.2, hl₄_def.1, hl₄_def.2, l₂, l₁, O1]
  -- Very ugly, but whatever...
  field_simp
  simp [← neg_mul, ← div_mul_div_comm, ← div_mul_div_comm, mul_div_assoc, div_self, mul_div_assoc, sub_eq_add_neg, ← mul_assoc, ← neg_div, neg_sub]
  field_simp
  ring_nf
  simp
  symm
  have : -((z₂.re : ℂ) * (z₁.im : ℂ)) + (z₂.im : ℂ) * (z₁.re : ℂ) ≠ 0 := by
    norm_cast
    -- Why is it important for z₁ and z₂ to be non-orthogonal?
    sorry
  calc
    _ = z₁ * (-(↑z₂.re * ↑z₁.im) + ↑z₂.im * ↑z₁.re)
        * ↑(Complex.abs z₂) * ↑(Complex.abs z₁) ^ 2 / (↑(Complex.abs z₁) ^ 2 * ↑(Complex.abs z₂) *
        (-(↑z₂.re * ↑z₁.im) + ↑z₂.im * ↑z₁.re)) := by ring
    _ = z₁ * (-(↑z₂.re * ↑z₁.im) + ↑z₂.im * ↑z₁.re)
        * ↑(Complex.abs z₂) * ↑(Complex.abs z₁) ^ 2 / ↑(Complex.abs z₁) ^ 2 / ↑(Complex.abs z₂)
        / (-(↑z₂.re * ↑z₁.im) + ↑z₂.im * ↑z₁.re) := by simp [← div_div]
    _ = z₁ * ((-(↑z₂.re * ↑z₁.im) + ↑z₂.im * ↑z₁.re)
        * (↑(Complex.abs z₁) ^ 2 / ↑(Complex.abs z₁) ^ 2) * (↑(Complex.abs z₂) / ↑(Complex.abs z₂))
        / (-(↑z₂.re * ↑z₁.im) + ↑z₂.im * ↑z₁.re)) := by ring
    _ = z₁ := by
          simp [div_self, hz₁_ne_zero, hz₂_ne_zero, this]

lemma 𝕆_real_mul {z : ℂ} {a : ℝ} (hz : z ∈ 𝕆) : a * z ∈ 𝕆 := by sorry
lemma 𝕆_i_mul {z : ℂ} (hz : z ∈ 𝕆) : Complex.I * z ∈ 𝕆 := by sorry

lemma 𝕆_neg {z : ℂ} (hz : z ∈ 𝕆) : -z ∈ 𝕆 := by rw [neg_eq_neg_one_mul]; norm_cast; exact 𝕆_real_mult hz
