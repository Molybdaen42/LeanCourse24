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
lemma E1 {z : ℂ} {l : line} (hz : z ∈ 𝕆) (hl : l ∈ 𝕆.lines) :
  (⟨z,z - l.vec,(by simp [sub_eq_neg_add, vec_ne_zero l])⟩ : line) ∈ 𝕆.lines := by
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
