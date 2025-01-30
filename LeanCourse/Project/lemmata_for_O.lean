import LeanCourse.Project.defs
open Classical
open Construction
open ComplexConjugate

section Proof_simplifying_lemmata
/- **Some Lemmata for 𝕆ₙ and 𝕆 that simplify proofs** -/

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
      left; use l; simp; exact im h' hl
    · have : n = m + 1 := by linarith
      rw [this]


-- The following lemmata allow us to improve the structure of our proofs
lemma in_𝕆_if_eq (z : ℂ) {z' : ℂ} : z ∈ 𝕆 → z' = z → z' ∈ 𝕆 := by
  intro hz h
  rw [h]
  assumption
lemma in_𝕆_lines_if_eq (l : line) {l' : line} : l ∈ 𝕆.lines → l'.eq l → l' ∈ 𝕆.lines := by
  intro hl h
  simp [𝕆.lines] at *
  obtain ⟨i,hi⟩ := hl
  use i+1
  left
  use l
lemma in_𝕆_lines_if_eqq (l : line) {l' : line} : l ∈ 𝕆.lines → l' = l → l' ∈ 𝕆.lines := by
  intro hl h
  rw [h]
  assumption

end Proof_simplifying_lemmata
section Axioms_in_𝕆
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

end Axioms_in_𝕆
section Random_stuff
-- **More random but useful stuff**

/-- |z|^2 = (z.re : ℂ)^2 + (z.im : ℂ)^2-/
lemma Complex.sq_abs_eq {z : ℂ} : (Complex.abs z)^2 = (z.re : ℂ)^2 + (z.im : ℂ)^2 := by
  norm_cast
  simp [← Complex.sq_abs_sub_sq_im]
/-- |z|^2 = z.re^2 + z.im^2-/
lemma Complex.sq_abs_eq_in_ℝ {z : ℂ} : (Complex.abs z)^2 = (z.re)^2 + (z.im)^2 := by
  simp [← Complex.sq_abs_sub_sq_im]

/-- If z ≠ 0, |z|/|z| = 1.-/
lemma div_abs {z : ℂ} (h : z ≠ 0) : (Complex.abs z : ℂ)/(Complex.abs z : ℂ) = 1 := by
  norm_cast
  exact div_self ((AbsoluteValue.ne_zero_iff Complex.abs).mpr h)

/-- O4(z,l) is not parallel to l.-/
lemma O4_not_parallel {l : line} {z : ℂ} :
  ¬AreParallel l (O4 z l) := by
    simp [AreParallel, O4, line.vec, div_self vec_well_defined]
    rw [← line.vec]
    constructor
    · -- Essentially to show: 1 ≠ Complex.I
      by_contra h
      have := (mul_eq_right₀ (vec_ne_zero l)).mp h.symm
      simp [Complex.ext_iff] at this
    · -- Essentially to show: 1 ≠ -Complex.I
      by_contra h
      rw [← neg_mul] at h
      have := (mul_eq_right₀ (vec_ne_zero l)).mp h.symm
      simp [Complex.ext_iff] at this
/-- O4(z,l) is perpendicular to l.-/
lemma O4_perpendicular {l : line} {z : ℂ} :
  (l.vec * conj (O4 z l).vec).re = 0 := by
    simp [O4, line.vec, div_self vec_well_defined]
    ring


-- From now on all proofs are structured like this:
/-
1. Construct a point equaling the searched number
  by using axioms or prior lemmata or theorems.
2. apply in_𝕆_if_eq (constructed point)
3. Show that the constructed point lies in 𝕆
  (It's not longer necessary to dive into the definition of 𝕆.
  Lemmata like O4_in_𝕆 suffice.)
4. Show that the constructed point equals the searched number.
-/
