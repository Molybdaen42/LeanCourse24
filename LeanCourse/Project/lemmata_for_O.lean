import LeanCourse.Project.defs
open Classical
open Construction
open ComplexConjugate

/- **Some Lemmata for 𝕆** -/

/-- 𝕆ₙ.points is increasing.-/
lemma 𝕆ₙ.points_inc (n m : ℕ) (h: n ≤ m) : 𝕆ₙ.points n ⊆ 𝕆ₙ.points m := by
  induction m with
  | zero => simp at h; simp [h]
  | succ m im =>
    by_cases h' : n ≤ m
    · -- sps. n ≤ m and z ∈ points n
      intro z hz
      -- then z ∈ points m
      specialize im h' hz
      -- to show: z ∈ points (m+1)
      left; assumption
    · have : n = m + 1 := by linarith
      rw [this]

/-- 𝕆ₙ.lines is increasing.-/
lemma 𝕆ₙ.lines_inc (n m : ℕ) (h: n ≤ m) : 𝕆ₙ.lines n ⊆ 𝕆ₙ.lines m := by
  induction m with
  | zero => simp at h; simp [h]
  | succ m im =>
    by_cases h' : n ≤ m
    · -- sps. n ≤ m and l ∈ lines n
      intro l hl
      -- to show: l ∈ lines (m+1)
      -- We know that l ∈ lines m by induction
      left; exact im h' hl
    · have : n = m + 1 := by linarith
      rw [this]

lemma O4_not_parallel {l : line} {z : ℂ} :
  ¬AreParallel l (O4 z l) := by
    simp [AreParallel, O4, line.vec, div_self vec_well_defined]
    have : IsRightCancelMul ℂ := by sorry
    constructor
    · rw [← one_mul ((l.z₂ - l.z₁) / (Complex.abs (l.z₂ - l.z₁))), ← mul_assoc, mul_one]
      apply (mul_ne_mul_left ((l.z₂ - l.z₁) / (Complex.abs (l.z₂ - l.z₁)))).mpr
      simp [Complex.ext_iff]
    · rw [← one_mul ((l.z₂ - l.z₁) / (Complex.abs (l.z₂ - l.z₁))), ← mul_assoc, mul_one, ← neg_mul]
      apply (mul_ne_mul_left ((l.z₂ - l.z₁) / (Complex.abs (l.z₂ - l.z₁)))).mpr
      simp [Complex.ext_iff]
lemma O4_perpendicular {l : line} {z : ℂ} :
  (l.vec * conj (O4 z l).vec).re = 0 := by
    simp [O4, line.vec, div_self vec_well_defined]
    ring


/- **Lemmata for the axioms being in 𝕆 if used on elements of 𝕆** -/

/-- The result of O1 is in 𝕆 if the arguments are in 𝕆.-/
lemma O1_in_𝕆 {z₁ z₂ : ℂ} {h : z₁ ≠ z₂} (hz₁ : z₁ ∈ 𝕆) (hz₂ : z₂ ∈ 𝕆) : O1 z₁ z₂ h ∈ 𝕆.lines := by
  simp [𝕆, 𝕆.lines] at *
  obtain ⟨N₁,hz₁N⟩ := hz₁
  obtain ⟨N₂,hz₂N⟩ := hz₂
  let N := max N₁ N₂

  use N+1
  right; left -- O1
  use z₁ -- first argument
  constructor; apply 𝕆ₙ.points_inc N₁ N (le_max_left N₁ N₂); exact hz₁N
  use z₂ -- second argument
  constructor; apply 𝕆ₙ.points_inc N₂ N (le_max_right N₁ N₂); exact hz₂N
  use h
  simp

/-- The result of O2 is in 𝕆 if the arguments are in 𝕆.-/
lemma O2_in_𝕆 {z₁ z₂ : ℂ} {h : z₁ ≠ z₂} (hz₁ : z₁ ∈ 𝕆) (hz₂ : z₂ ∈ 𝕆) : O2 z₁ z₂ h ∈ 𝕆.lines := by
  simp [𝕆, 𝕆.lines] at *
  obtain ⟨N₁,hz₁N⟩ := hz₁
  obtain ⟨N₂,hz₂N⟩ := hz₂
  let N := max N₁ N₂

  use N+1
  right; right; left -- O2
  use z₁ -- first argument
  constructor; apply 𝕆ₙ.points_inc N₁ N (le_max_left N₁ N₂); exact hz₁N
  use z₂ -- second argument
  constructor; apply 𝕆ₙ.points_inc N₂ N (le_max_right N₁ N₂); exact hz₂N
  use h
  simp

/-- The result of O3 is in 𝕆 if the arguments are in 𝕆.-/
lemma O3_in_𝕆 {l₁ l₂ : line} (hl₁ : l₁ ∈ 𝕆.lines) (hl₂ : l₂ ∈ 𝕆.lines) : O3 l₁ l₂ ∈ 𝕆.lines := by
  simp [𝕆.lines] at *
  obtain ⟨N₁,hl₁N⟩ := hl₁
  obtain ⟨N₂,hl₂N⟩ := hl₂
  let N := max N₁ N₂

  use N+1
  right; right; right; left -- O3
  use l₁ -- first argument
  constructor; apply 𝕆ₙ.lines_inc N₁ N (le_max_left N₁ N₂); exact hl₁N
  use l₂ -- second argument
  constructor; apply 𝕆ₙ.lines_inc N₂ N (le_max_right N₁ N₂); exact hl₂N
  simp

/-- The result of O3' is in 𝕆 if the arguments are in 𝕆.-/
lemma O3'_in_𝕆 {l₁ l₂ : line} (hl₁ : l₁ ∈ 𝕆.lines) (hl₂ : l₂ ∈ 𝕆.lines) : O3' l₁ l₂ ∈ 𝕆.lines := by
  simp [𝕆.lines] at *
  obtain ⟨N₁,hl₁N⟩ := hl₁
  obtain ⟨N₂,hl₂N⟩ := hl₂
  let N := max N₁ N₂

  use N+1
  right; right; right; right; left -- O3'
  use l₁ -- first argument
  constructor; apply 𝕆ₙ.lines_inc N₁ N (le_max_left N₁ N₂); exact hl₁N
  use l₂ -- second argument
  constructor; apply 𝕆ₙ.lines_inc N₂ N (le_max_right N₁ N₂); exact hl₂N
  simp

/-- The result of O4 is in 𝕆 if the arguments are in 𝕆.-/
lemma O4_in_𝕆 {z : ℂ} {l : line} (hz : z ∈ 𝕆) (hl : l ∈ 𝕆.lines) : O4 z l ∈ 𝕆.lines := by
  simp [𝕆,𝕆.lines] at *
  obtain ⟨N₁,hzN⟩ := hz
  obtain ⟨N₂,hlN⟩ := hl
  let N := max N₁ N₂

  use N+1
  right; right; right; right; right; left -- O4
  use z -- first argument
  constructor; apply 𝕆ₙ.points_inc N₁ N (le_max_left N₁ N₂); exact hzN
  use l -- second argument
  constructor; apply 𝕆ₙ.lines_inc N₂ N (le_max_right N₁ N₂); exact hlN
  simp

/-- The result of O5 is in 𝕆 if the arguments are in 𝕆.-/
lemma O5_in_𝕆 {z₁ z₂ : ℂ} {h : z₁ ≠ z₂} {l : line} (hz₁ : z₁ ∈ 𝕆) (hz₂ : z₂ ∈ 𝕆) (hl : l ∈ 𝕆.lines) : O5 z₁ z₂ h l ⊆ 𝕆.lines := by
  simp [𝕆,𝕆.lines] at *
  obtain ⟨N₁,hz₁N⟩ := hz₁
  obtain ⟨N₂,hz₂N⟩ := hz₂
  obtain ⟨N₃,hlN⟩ := hl
  let N := max (max N₁ N₂) N₃

  intro element h_element
  simp
  use N+1
  right; right; right; right; right; right; left -- O5
  use z₁ -- first argument
  constructor; apply 𝕆ₙ.points_inc N₁ N (by omega); exact hz₁N
  use z₂ -- first argument
  constructor; apply 𝕆ₙ.points_inc N₂ N (by omega); exact hz₂N
  use h
  use l -- third argument
  constructor; apply 𝕆ₙ.lines_inc N₃ N (by omega); exact hlN
  use element
  simp [h_element]

/-- The result of O6 is in 𝕆 if the arguments are in 𝕆.-/
lemma O6_in_𝕆 {z₁ z₂ : ℂ} {h : z₁ ≠ z₂} {l₁ l₂ : line} (hz₁ : z₁ ∈ 𝕆) (hz₂ : z₂ ∈ 𝕆) (hl₁ : l₁ ∈ 𝕆.lines) (hl₂ : l₂ ∈ 𝕆.lines) : O6 z₁ z₂ h l₁ l₂ ⊆ 𝕆.lines := by
  simp [𝕆,𝕆.lines] at *
  obtain ⟨N₁,hz₁N⟩ := hz₁
  obtain ⟨N₂,hz₂N⟩ := hz₂
  obtain ⟨N₃,hl₁N⟩ := hl₁
  obtain ⟨N₄,hl₂N⟩ := hl₂
  let N := max (max N₁ N₂) (max N₃ N₄)

  intro element h_element
  simp
  use N+1
  right; right; right; right; right; right; right -- O6
  use z₁ -- first argument
  constructor; apply 𝕆ₙ.points_inc N₁ N (by omega); exact hz₁N
  use z₂ -- first argument
  constructor; apply 𝕆ₙ.points_inc N₂ N (by omega); exact hz₂N
  use h
  use l₁ -- third argument
  constructor; apply 𝕆ₙ.lines_inc N₃ N (by omega); exact hl₁N
  use l₂ -- third argument
  constructor; apply 𝕆ₙ.lines_inc N₄ N (by omega); exact hl₂N
  use element
  simp [h_element]

/-- The intersection of two non-parallel lines out of 𝕆 lies in 𝕆.-/
lemma Isect_in_𝕆 {l₁ l₂ : line} {h : ¬AreParallel l₁ l₂} (hl₁ : l₁ ∈ 𝕆.lines) (hl₂ : l₂ ∈ 𝕆.lines) : Isect l₁ l₂ h ∈ 𝕆 := by
  simp [𝕆,𝕆.lines] at *
  obtain ⟨N₁,hl₁N⟩ := hl₁
  obtain ⟨N₂,hl₂N⟩ := hl₂
  let N := max N₁ N₂

  use N+1
  right -- Isect
  use l₁ -- first argument
  constructor; apply 𝕆ₙ.lines_inc N₁ N (le_max_left N₁ N₂); exact hl₁N
  use l₂ -- second argument
  constructor; apply 𝕆ₙ.lines_inc N₂ N (le_max_right N₁ N₂); exact hl₂N
  use h


-- **Two Folding Lemmata**


/-- Given a point z and a line l, fold a line parallel to l that goes through z.-/
lemma E1 (z : ℂ) (l : line) (hz : z ∈ 𝕆) (hl : l ∈ 𝕆.lines) :
  ∃ l' ∈ 𝕆.lines, l'.z₁ = z ∧ l'.z₂ = z - l.vec := by
    -- Will show: it's O4(z, O4(z, l))
    simp [𝕆.lines, 𝕆] at hl hz ⊢
    -- z lies in 𝕆ₙ₁ and l in 𝕆ₙ₂.
    obtain ⟨n1, hln⟩ := hl
    obtain ⟨n2, hzn⟩ := hz
    -- choose the bigger one of n1 and n2
    let n := max n1 n2
    -- then z and l ∈ 𝕆ₙ
    have hzn := 𝕆ₙ.points_inc n2 n (Nat.le_max_right n1 n2) hzn
    have hln := 𝕆ₙ.lines_inc n1 n (Nat.le_max_left n1 n2) hln

    -- the second argument, O4(z, l), lies in 𝕆ₙ₊₁
    have : O4 z l ∈ 𝕆ₙ.lines (n+1) := by
      -- well, use O4 z l, of course
      simp; right; right; right; right; right; left -- O4
      tauto

    use ⟨z,z - l.vec,(by simp [sub_eq_neg_add, vec_ne_zero l])⟩
    symm; constructor; simp [line.vec]

    -- the final line is in 𝕆ₙ₊₂
    use n + 2
    right; right; right; right; right; left -- O4
    use z -- first argument
    constructor; left; exact hzn
    use O4 z l -- second argument
    constructor; exact this
    -- still left to show that the built line is equal to O4 z (O4 z l)
    simp [O4, line.vec]
    field_simp
    simp [mul_div_assoc, sub_eq_add_neg, ← mul_assoc, ← neg_div, neg_sub]
    rfl

/-- Given a point z and a line l, reflect z across l.-/
-- 2 * (l.z₁ + ⟨z-l.z₁,l.vect⟩ * l.vec) - z
-- = 2 * (l.z₁ + ((z-l.z₁)*conj l.vec).re * l.vec) - z
lemma E2 (z : ℂ) (l : line) (hz : z ∈ 𝕆) (hl : l ∈ 𝕆.lines) :
  2 * (l.z₁ + ((z-l.z₁) * conj l.vec).re * l.vec) - z ∈ 𝕆 := by
    -- l₁ is perpendicular to l and passes through z.
    let l₁ := O4 z l
    have hl₁ : l₁ ∈ 𝕆.lines := O4_in_𝕆 hz hl

    -- l₂ is parallel to l and passes through z.
    let ⟨l₂,hl₂,hl₂_def1,hl₂_def2⟩ := E1 z l hz hl
    have hl₁_l₂_not_parallel : ¬AreParallel l₁ l₂ := by 
      simp [AreParallel, line.vec]
      simp [l₁, O4, hl₂_def1, hl₂_def2]
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

    -- l₃ bisects the angle between l₁ and l₂. The three of them intersect in z.
    let l₃ := O3 l₁ l₂
    have hl₃ : l₃ ∈ 𝕆.lines := O3_in_𝕆 hl₁ hl₂
    have hl₃_z₁ : l₃.z₁ = z := by
      simp [l₃, O3, hl₁_l₂_not_parallel, Isect, l₁]
      simp [O4, line.vec, div_self vec_well_defined, hl₂_def1]
    have hl₃_z₂ : l₃.z₂ = z + Complex.I * l.vec - l.vec := by
      simp [l₃, O3, hl₁_l₂_not_parallel, Isect, l₁]
      simp [O4, line.vec, div_self vec_well_defined]
      simp [hl₂_def1, hl₂_def2, vec_abs_one]
      rfl
    have hl_l₃_not_parallel : ¬AreParallel l l₃ := by 
      simp [AreParallel]
      rw [line.vec, line.vec, hl₃_z₁, hl₃_z₂, ← line.vec]
      ring; field_simp
      constructor
      · intro h
        have h : l.vec * Complex.abs (Complex.I * l.vec - l.vec) =
  Complex.I * l.vec / ↑(Complex.abs (Complex.I * l.vec - l.vec)) - l.vec / ↑(Complex.abs (Complex.I * l.vec - l.vec)) * Complex.abs (Complex.I * l.vec - l.vec) := by 
          sorry
        field_simp [vec_ne_zero] at h
        --have := mul_eq_mul_right_iff.mpr this
        --apply mul_eq_mul_right_iff.mpr (Complex.abs (Complex.I * l.vec - l.vec)) at h
        sorry
      · sorry

    -- z₁ is the intersection of l and l₃.
    let z₁ := Isect l l₃ hl_l₃_not_parallel
    have hz₁ : z₁ ∈ 𝕆 := Isect_in_𝕆 hl hl₃

    -- l₄ is orthogonal to l₃ and goes through z₁.
    let l₄ := O4 z₁ l₃
    have hl₄ : l₄ ∈ 𝕆.lines := O4_in_𝕆 hz₁ hl₃
    have hl₁_l₄_not_parallel : ¬AreParallel l₁ l₄ := by sorry

    -- The result is the intersection of l₁ and l₄.
    -- But first, let's compute some stuff
    
    -- Is there a neat formula for z₁? If yes, write is as above.
    have h : z₁ = Isect l l₃ hl_l₃_not_parallel := by rfl
    simp [Isect, line.vec, hl₃_z₁, hl₃_z₂] at h
    field_simp [vec_well_defined] at h
    simp [mul_comm, add_comm, ← add_sub] at h
    -- Iwie muss man ja Complex.abs (l.z₂ - l.z₁) und das andere Complex.abs rausteilen können
    --field_simp [div_self vec_well_defined] at h



    -- The result is the intersection of l₁ and l₄.
    have : 2 * (l.z₁ + (z-l.z₁) * conj l.vec * l.vec) - z = Isect l₁ l₄ hl₁_l₄_not_parallel := by
      --simp [Isect, l₄, O4]
      --field_simp [line.vec, div_self vec_well_defined]
      --simp [hl₃_z₁, hl₃_z₂]

      --simp [line.vec]
      --field_simp [line.vec, div_self vec_well_defined]
      --simp [Isect, l₁, O4, line.vec, hl₂_def1, hl₂_def2]
      --field_simp [line.vec, div_self vec_well_defined]
      --ring
      --field_simp
      --simp [div_self vec_well_defined]
      sorry
    -- Again: The result is the intersection of l₁ and l₄.
    rw [this]
    exact Isect_in_𝕆 hl₁ hl₄

lemma E2' (z : ℂ) (l : line) (hz : z ∈ 𝕆) (hl : l ∈ 𝕆.lines) :
  ∃ z' ∈ 𝕆, ∃ (h : z ≠ z'), (O2 z z' h).eq l := by
    let z' := 2 * (l.z₁ + ((z-l.z₁) * conj l.vec).re * l.vec) - z
    have z'_ne_z : z' ≠ z := by 
      simp_rw [z', line.vec]
      ring
      sorry
    use z';
    constructor; exact E2 z l hz hl
    use z'_ne_z.symm;
    apply (line_eq_symm (O2 z z' z'_ne_z.symm) l).mpr
    apply (line_eq_iff_both_points_lie_in_the_other' l (O2 z z' z'_ne_z.symm)).mpr
    simp [O2, z']
    constructor
    · ring
      
      sorry
    · sorry



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

lemma conj_in_𝕆 {z : ℂ} (hz : z ∈ 𝕆) : conj z ∈ 𝕆 := by
  -- Use E2 on the real axis
  sorry
