import LeanCourse.Project.defs
open Classical
open Construction

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
lemma E2 {z : ℂ} {l : line} (hz : z ∈ 𝕆) (hl : l ∈ 𝕆.lines) :
  sorry ∈ 𝕆 := by
    -- l₁ := O4(z, l) is perpendicular to l and passes through z
    let l₁ := O4 z l
    -- pick z' on l that is not on l₁ (l.z₁ or l.z₂ will work)
    have : ∃ z' ∈ l.points, z' ∉ l₁.points := by
      by_cases h : l.z₁ ∈ l₁.points
      · use l.z₂
        constructor
        · exact z₂_on_l l
        · sorry
      · use l.z₁
        exact ⟨z₁_on_l l, h⟩
    obtain ⟨z', hz'1, hz'2⟩ := this
    -- Now we apply O5 to z, z' and l₁ to fold z over l
    let L₂ := O5 z z' (by sorry) l₁
    have : Nonempty L₂ := by sorry
    obtain ⟨l₂,hl₂⟩ := this
    -- We keep our plane folded. While folded, we can mark the line going through z and z'. This marks the point z'', which is the reflection of z across l.
    sorry

noncomputable def reAxis : line := O1 0 1 zero_ne_one
noncomputable def imAxis : line := O4 0 reAxis
lemma reAxis_in_𝕆 : reAxis ∈ 𝕆.lines := by sorry -- take the code from i_in_𝕆
lemma imAxis_in_𝕆 : imAxis ∈ 𝕆.lines := by sorry

lemma i_in_𝕆 : Complex.I ∈ 𝕆 := by
  -- first define all necessary lines and points
  let reAxis : line := O1 0 1 (zero_ne_one)
  let imAxis : line := O4 0 reAxis
  let l₁ : line := O4 1 reAxis
  let l₂ : line := O3' reAxis l₁
  -- Complex.I = Isect imAxis l₂

  /- Maybe the following code would work if it would be more efficient.
  Now the time limiter stops the computation at simp [generate_lines].

  simp [𝕆]
  use 4
  simp [generate_lines]
  -/

  -- then show that they lie in 𝕆₁ or 𝕆₂
  have h1 : reAxis ∈ 𝕆ₙ.lines 1 := by
    -- Want to use O1(0, 1)
    -- simp does everything
    simp [generate_lines, line.eq]
  have h2 : imAxis ∈ 𝕆ₙ.lines 2 := by
    simp at h1
    -- Want to use O4(0, reAxis)
    right; right; right; right; right; left -- O4
    use 0; simp -- first argument
    use reAxis; simp [h1] -- second argument
  have h3 : l₁ ∈ 𝕆ₙ.lines 2 := by
    -- Want to use O4(1, reAxis)
    right; right; right; right; right; left -- O4
    use 1; -- first argument
    constructor; simp -- 1 lies in 𝕆₁
    use reAxis -- second argument
    constructor; exact h1 -- reAxis lies in 𝕆₁
    simp
  have h4 : l₂ ∈ 𝕆ₙ.lines 3 := by
    -- Want to use O3'(reAxis, l₁)
    right; right; right; right; left -- O3'
    use reAxis -- first argument
    constructor; left; exact h1 -- reAxis lies in 𝕆₂
    use l₁ -- Second argument of O3'(reAxis, l₁)
    constructor; exact h3 -- l₁ lies in 𝕆₂
    simp
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
  simp [𝕆]
  use 4
  -- Complex.I = Isect imAxis l₂
  right;
  use imAxis
  constructor; left; exact h2 -- imAxis ∈ 𝕆₃
  use l₂
  constructor; exact h4 -- l₂ ∈ 𝕆₃
  use h5 -- imAxis and l₂ are not parallel
  simp [Isect, imAxis, O4, reAxis, O1, l₁, l₂, line.vec, O3', AreParallel, I_ne_one_or_neg_one, Complex.abs, Complex.normSq]


-- **Field Operations**

lemma 𝕆_real_mult {z : ℂ} {a : ℝ} (hz : z ∈ 𝕆) : a * z ∈ 𝕆 := by sorry

lemma 𝕆_neg {z : ℂ} (hz : z ∈ 𝕆) : -z ∈ 𝕆 := by rw [neg_eq_neg_one_mul]; norm_cast; exact 𝕆_real_mult hz

/--𝕆 is closed under addition.-/
theorem 𝕆_add {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ 𝕆) (hz₂ : z₂ ∈ 𝕆) : z₁ + z₂ ∈ 𝕆 := by
  -- Wlog we can assume that z₁ and z₂ are not equal to 0 or to a multiple (by a real number) of each other
  by_cases hz₁_ne_zero : z₁ = 0; simp [hz₁_ne_zero, hz₂]
  by_cases hz₂_ne_zero : z₂ = 0; simp [hz₂_ne_zero, hz₁]
  by_cases hz₁_ne_real_mult_z₂ : ∃ a : ℝ, z₁ = a * z₂
  · -- ToDo: Want to do this without using the multiplication lemma
    -- in order to use addition in there
    obtain ⟨a,ha⟩ := hz₁_ne_real_mult_z₂
    simp [ha, ← add_one_mul]
    norm_cast
    exact 𝕆_real_mult hz₂
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

  have hl₁_n : l₁ ∈ 𝕆ₙ.lines (N+1) := by
    right; left -- O1
    use 0 -- first argument
    constructor; apply 𝕆ₙ.points_inc 0 N (Nat.zero_le N); simp
    use z₁ -- second argument
    constructor; apply 𝕆ₙ.points_inc N₁ N (Nat.le_max_left N₁ N₂); exact hz₁N
    use hz₁_ne_zero.symm
    simp [l₁]
  have hl₂_n : l₂ ∈ 𝕆ₙ.lines (N+1) := by
    right; left -- O1
    use 0 -- first argument
    constructor; apply 𝕆ₙ.points_inc 0 N (Nat.zero_le N); simp
    use z₂ -- second argument
    constructor; apply 𝕆ₙ.points_inc N₂ N (Nat.le_max_right N₁ N₂); exact hz₂N
    use hz₂_ne_zero.symm
    simp [l₂]

  have hl₁ : l₁ ∈ 𝕆.lines := by simp [𝕆.lines]; use (N+1); exact hl₁_n
  have hl₂ : l₂ ∈ 𝕆.lines := by simp [𝕆.lines]; use (N+1); exact hl₂_n

  -- Second step: fold a line parallel to l₁ that goes through z₂
  -- and a line parallel to l₂ that goes through z₁.
  let ⟨l₃,hl₃,hl₃_def⟩ := E1 z₂ l₁ hz₂ hl₁
  let ⟨l₄,hl₄,hl₄_def⟩ := E1 z₁ l₂ hz₁ hl₂

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
  simp --[mul_comm]
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
