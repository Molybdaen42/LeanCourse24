import Mathlib.Data.Complex.Basic
import Mathlib.Order.Basic
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord

open ComplexConjugate
open Classical

/-
In this file we will define the origami numbers and their axiomatic operations.
-/

namespace Construction

/-- A line in ℂ is a structure consisting of two different points z₁ and z₂ ∈ ℂ.
The set of points of the line are defined in line.points.
A normalised direction vector of the line is given in line.vec.-/
structure line where
  (z₁ z₂ : ℂ) (z₁_neq_z₂ : z₁ ≠ z₂)

/-- The points of a line given by two different points z₁ and z₂ are
 the linear combinations of these two points.-/
@[simp] def line.points (l : line) : Set ℂ := {(t : ℂ) * l.z₁ + (1-t) * l.z₂ | (t : ℝ)}

/-- A normalised direction vector of the line.-/
--@[simp]
noncomputable def line.vec (l : line) : ℂ := (l.z₂ - l.z₁) / (Complex.abs (l.z₂ - l.z₁))

/-- The denominator of line.vec is ≠ 0. Maybe not necessary per definition of Complex.inv... -/
@[simp] lemma vec_well_defined {l : line} : Complex.abs (l.z₂ - l.z₁) ≠ 0 := by simp [l.z₁_neq_z₂.symm]

variable (l : line)

/-- The direction vector is never zero.-/
lemma vec_ne_zero (l : line) : l.vec ≠ 0 := by
  unfold line.vec
  simp
  constructor
  · apply sub_ne_zero_of_ne
    exact l.z₁_neq_z₂.symm
  · exact l.z₁_neq_z₂.symm

/-- The direction vector is of length one.-/
lemma vec_abs_one (l : line) : Complex.abs l.vec = 1 := by
  field_simp [line.vec, vec_well_defined]

/-- The term z₂ - z₁ is never zero.-/
lemma diff_ne_zero (l : line) : l.z₂ - l.z₁ ≠ 0 := by
  exact sub_ne_zero_of_ne l.z₁_neq_z₂.symm
/-- The term z₂ - z₁ is never zero.-/
lemma diff_ne_zero' (l : line) : l.z₁ - l.z₂ ≠ 0 := by
  exact sub_ne_zero_of_ne l.z₁_neq_z₂

lemma z₁_on_l (l : line) : l.z₁ ∈ l.points := by use 1; simp
lemma z₂_on_l (l : line) : l.z₂ ∈ l.points := by use 0; simp

/-- The minimal distance between a point z and a line l.-/
noncomputable def dist_point_line (z : ℂ) (l : line) : ℝ :=
  Complex.abs ((l.z₁-z) - ((l.z₁-z)*conj l.vec).re * l.vec)
-- formula from https://en.wikipedia.org/wiki/Distance_from_a_point_to_a_line#Vector_formulation
-- (a * conj b).re is the same as the dot product of a and b viewed as 2-dim. vectors


-- **Define an equivalence relation on line representing equality of lines**

/-- Two lines are equal to one another iff they have the same set of points.
  Attention: l₁.eq l₂ is not the same as l₁ = l₂!
  Using the first one will satisfy our needs while the other one requires equal generationg points z₁ and z₂.-/
def line.eq (l₁ l₂ : line) := l₁.points = l₂.points

@[symm] lemma line_eq_symm (l₁ l₂ : line) : l₁.eq l₂ ↔ l₂.eq l₁ := by rw [line.eq, line.eq]; tauto
@[symm] lemma line_eq_symm' (l₁ l₂ : line) : ¬l₁.eq l₂ ↔ ¬l₂.eq l₁ := by rw [not_iff_not]; exact line_eq_symm l₁ l₂

-- show that line.eq is in fact an equivalence relation
lemma line_eq_is_equivalence_relation : Equivalence line.eq := by
  unfold line.eq
  constructor
  · -- to show: reflexive
    tauto
  · -- to show: symmetric
    tauto
  · -- to show: transitive
    intro l₁ l₂ l₃ h12 h13
    rw [h12]
    assumption

@[simp] lemma line_eq_self (l : line) : l.eq l := by
  simp [line_eq_is_equivalence_relation.refl]

lemma line_eq_if_switched_points (l : line) : l.eq ⟨l.z₂, l.z₁, l.z₁_neq_z₂.symm⟩ := by
  ext z
  constructor
  · rintro ⟨t,ht⟩
    use 1-t
    simp [← ht, add_comm]
  · rintro ⟨t,ht⟩
    use 1-t
    simp [← ht, add_comm]

/-- Two lines l₁ and l₂ are equal iff l₁.z₁ and l₁.z₂ lie in l₂.-/
lemma line_eq_iff_both_points_lie_in_the_other (l₁ l₂ : line) :
  l₁.eq l₂ ↔ l₁.z₁ ∈ l₂.points ∧ l₁.z₂ ∈ l₂.points := by
    unfold line.eq
    constructor
    · intro h
      rw [← h]
      constructor
      · use 1; simp
      · use 0; simp
    · intro ⟨⟨t1,h1⟩,⟨t2,h2⟩⟩
      ext z
      constructor
      · intro ⟨t3,h3⟩
        use t3*t1 - t3*t2 + t2
        simp [←h1,←h2,←h3]
        ring
      · intro ⟨t3,h3⟩
        use (t3 - t2) / (t1 - t2)
        simp [←h1,←h2,←h3]
        have : (t1 - t2 : ℂ) ≠ 0 := by
          -- to show: t1 ≠ t2
          apply sub_ne_zero_of_ne
          -- suppose they are equal
          by_contra h
          -- then l₁.z₁ = l₁.z₂
          rw [← h, h1] at h2
          -- but we assumed that they do not equal each other
          have := l₁.z₁_neq_z₂
          contradiction
        calc
          _ = ((t3 - t2)/(t1 - t2) * (t1-t2) + t2) * l₂.z₁ + (- (t3 - t2)/(t1 - t2) * (t1 - t2) + (1-t2)) * l₂.z₂ := by ring
          _ = t3 * l₂.z₁ + (1 - t3) * l₂.z₂ := by simp [this]
/-- Two lines l₁ and l₂ are equal iff l₂.z₁ and l₂.z₂ lie in l₁.-/
lemma line_eq_iff_both_points_lie_in_the_other' (l₁ l₂ : line) :
  l₁.eq l₂ ↔ l₂.z₁ ∈ l₁.points ∧ l₂.z₂ ∈ l₁.points := by
  rw [line_eq_symm]
  exact line_eq_iff_both_points_lie_in_the_other l₂ l₁


/-- Instead of z₂, we can use z₁ + k*vec for any k ≠ 0.-/
lemma line_eq_if_add_vec (l : line) {k : ℝ} (h : k ≠ 0) : l.eq ⟨l.z₁, l.z₁ + k*l.vec, (by simp [h, vec_ne_zero])⟩ := by
  -- first prove that |z₂ - z₁| ≠ 0
  have : (Complex.abs (l.z₂ - l.z₁) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr ((AbsoluteValue.ne_zero_iff Complex.abs).mpr (diff_ne_zero l))
  -- It's enough to show that l.z₁ and l.z₂ lie in the other line
  apply (line_eq_iff_both_points_lie_in_the_other l ⟨l.z₁, l.z₁ + k*l.vec, (by simp [h, vec_ne_zero])⟩).mpr
  -- Now it's pretty straightforward
  constructor
  · simp
    use 1
    simp
  · simp
    use 1 - (Complex.abs (l.z₂ - l.z₁)) / k
    simp [line.vec]
    ring_nf
    simp [h, this]

/-- Two lines are different if there is a point lying in one but not the other.-/
lemma line_ne_iff {l₁ l₂ : line} : (∃ x, x ∈ l₁.points ∧ x ∉ l₂.points) ↔ ¬l₁.eq l₂ := by
  constructor
  · rintro ⟨x, hx₁, hx₂⟩
    exact ne_of_mem_of_not_mem' hx₁ hx₂
  · intro h
    by_cases hz₁ : l₁.z₁ ∈ l₂.points
    · use l₁.z₂
      -- l₁.z₂ ∈ l₁.points
      constructor; exact z₂_on_l l₁
      -- Left to show: l₁.z₂ ∉ l₂.points
      -- Assume l₁.z₂ ∈ l₂.points
      by_contra hz₂
      -- Then ¬l₁.eq l₂ cannot be the case.
      rw [line_eq_iff_both_points_lie_in_the_other l₁ l₂, not_and] at h
      simp_rw [hz₁,hz₂] at h
      contradiction
    · -- Suppose l₁.z₁ ∉ l₂.points. Then take it.
      use l₁.z₁
      exact ⟨z₁_on_l l₁, hz₁⟩

/-- Two lines are different if there is a point lying in one but not the other.-/
lemma line_ne_iff' {l₁ l₂ : line} : (∃ x, x ∈ l₂.points ∧ x ∉ l₁.points) ↔ ¬l₁.eq l₂ := by
  rw [line_eq_symm]
  exact line_ne_iff


-- **What does it mean for two lines to be parallel?**

/-- Returns True if the lines are parallel and False otherwise.-/
def AreParallel (l₁ l₂ : line) : Prop := l₁.vec = l₂.vec ∨ l₁.vec = - l₂.vec

/-- l₁ is parallel to l₂ iff l₂ is parallel to l₁.-/
lemma Parallel_symm (l₁ l₂ : line) :  AreParallel l₁ l₂ ↔ AreParallel l₂ l₁ := by
  unfold AreParallel
  constructor
  · intro h
    obtain h1|h2 := h
    · left; symm; assumption
    · right; symm; exact neg_eq_iff_eq_neg.mpr h2
  · intro h
    obtain h1|h2 := h
    · left; symm; assumption
    · right; symm; exact neg_eq_iff_eq_neg.mpr h2

lemma Not_parallel_if_parallel (l₁ l₂ l₃ : line) : ¬AreParallel l₁ l₂ → AreParallel l₂ l₃ →   ¬AreParallel l₁ l₃ := by
  intro h' h
  unfold AreParallel at *
  push_neg at *
  constructor
  · obtain h1|h2 := h
    · rw [← h1]
      exact h'.1
    · rw[h2,neg_neg] at h'
      exact h'.2
  · obtain h1|h2 := h
    · rw[h1] at h'
      exact h'.2
    · rw[h2] at h'
      exact h'.1

-- Some other formulations of parallelity.
lemma AreParallel_if_disjoint (l₁ l₂ : line) : Disjoint l₁.points l₂.points → AreParallel l₁ l₂ := by
  unfold AreParallel Disjoint
  intro h
  by_contra hcontra
  push_neg at hcontra
  obtain ⟨h1,h2⟩ := hcontra
  sorry
lemma AreParallel_iff_forall (l₁ l₂ : line) :
  AreParallel l₁ l₂ ↔ ∀ z ∈ l₁.points, z + l₂.vec ∈ l₁.points := by
    sorry
lemma AreParallel_iff_forall' (l₁ l₂ : line) :
  AreParallel l₁ l₂ ↔ ∀ z ∈ l₂.points, z + l₁.vec ∈ l₂.points := by
    sorry


-- **intersection point of two lines**


/-- Computes the intersection point of l₁ and l₂.-/
-- The dot product of vectors v^⊥ and u is
-- the imaginary part of complex multiplication of v with the complex conjugate of u
noncomputable def Isect (l₁ l₂ : line) (h : ¬AreParallel l₁ l₂) : ℂ :=
  l₁.z₁ - (l₂.vec * conj (l₁.z₁ - l₂.z₁)).im / (l₂.vec * conj l₁.vec).im * l₁.vec
-- Is (h : ¬AreParallel l₁ l₂) a necessary/useful condition?
-- Maybe not, since /0 = 0 and


/- **The Axioms of origami number construction** -/

/-- Given two different points z₁ and z₂, we can fold a line that goes through both of them.-/
def O1 (z₁ z₂ : ℂ) (h : z₁ ≠ z₂) : line := {z₁ := z₁, z₂ := z₂, z₁_neq_z₂ := h : line}

/-- Given two different points z₁ and z₂, we can fold z₁ onto z₂
(i.e. find the perpendicular bisector of segment z₁z₂).-/
noncomputable def O2 (z₁ z₂ : ℂ) (h : z₁ ≠ z₂) : line where
  z₁ := (z₁+z₂)/2                      -- the midpoint of z₁ and z₂
  z₂ := (z₁+z₂)/2 + Complex.I*(z₂-z₁) -- turns the vector z₂-z₁ by 90° and adds it to the midpoint
  z₁_neq_z₂ := by
    field_simp
    simp
    exact sub_ne_zero_of_ne (id (Ne.symm h))

/-- Given two lines l₁ and l₂, we can fold l₁ onto l₂ (i.e. bisect the angle
between them). [Attention: There are two possibilities for the fold, the two of them being orthogonal to each other!]-/
noncomputable def O3 (l₁ l₂ : line) : line := if h : AreParallel l₁ l₂ then {
  z₁ := (l₁.z₁ + l₂.z₁)/2
  z₂ := (l₁.z₁ + l₂.z₂)/2
  z₁_neq_z₂ := by field_simp [l₂.z₁_neq_z₂]
} else {
  z₁ := Isect l₁ l₂ h
  z₂ := Isect l₁ l₂ h + l₁.vec + l₂.vec -- Be attentive to the signs!
  z₁_neq_z₂ := by
    simp [add_assoc]
    have : l₁.vec - (-l₂.vec) ≠ 0 := by
      unfold AreParallel at h
      push_neg at h
      exact sub_ne_zero_of_ne h.2
    simp [sub_eq_neg_add, add_comm] at this
    assumption
    -- TODO: Refactor this proof
}

/-- Given two lines l₁ and l₂, we can fold l₁ onto l₂ (i.e. bisect the angle
between them). [Attention: There are two possibilities for the fold, the two of them being orthogonal to each other!]-/
noncomputable def O3' (l₁ l₂ : line) : line := if h : AreParallel l₁ l₂ then {
  z₁ := (l₁.z₁ + l₂.z₁)/2
  z₂ := (l₁.z₁ + l₂.z₂)/2
  z₁_neq_z₂ := by field_simp [l₂.z₁_neq_z₂]
} else {
  z₁ := Isect l₁ l₂ h
  z₂ := Isect l₁ l₂ h + l₁.vec - l₂.vec -- Be attentive to the signs!
  z₁_neq_z₂ := by
    simp [add_sub_assoc]
    unfold AreParallel at h
    push_neg at h
    exact sub_ne_zero_of_ne h.1
}


/-- Given a point z and a line l, we can fold a line perpendicular to l that
goes through z.-/
noncomputable def O4 (z : ℂ) (l : line) : line where
  z₁ := z
  z₂ := z + Complex.I*l.vec
  z₁_neq_z₂ := by simp; exact vec_ne_zero l


/-- Given two points z₁ and z₂ and a line l, we can fold z₁ onto l with a
line that goes through z₂. There are 0, 1 or 2 solutions possible.-/
noncomputable def O5 (z₁ z₂ : ℂ) (h : z₁ ≠ z₂) (l : line) : Set line :=
  {l' : line | l'.z₁ = z₂ ∧
  2 * l'.z₂ - z₁ ∈ l.points ∧ Complex.abs (2 * l'.z₂ - z₁ - z₂) = Complex.abs (z₁-z₂)}


/--Given two points z₁ and z₂ and two lines l₁ and l₂, we can fold z₁ onto
l₁ and z₂ onto l₂ with a single line.-/
-- A line is a tangent to a parabola iff they have exactly one intersection point and the line is not orthogonal to the directrix of the parabola. Use this on the two parabolas with focal points z₁ resp. z₂ and directrix l₁ resp. l₂. The returned tangent line is the line generated by O6.
noncomputable def O6 (z₁ z₂ : ℂ) (h : z₁ ≠ z₂) (l₁ l₂ : line) : Set line :=
  {t : line |
  t.vec * conj l₁.vec ≠ 0 ∧ -- t.vec is not orthogonal to l₁.vec.
  t.vec * conj l₂.vec ≠ 0 ∧ -- t.vec is not orthogonal to l₂.vec.
  (∃ z ∈ t.points, Complex.abs (z-z₁) = dist_point_line z l₁ ∧ -- t is intersecting the parabola of z₁ and l₁ ...
  ∀ z' ∈ t.points, Complex.abs (z'-z₁) = dist_point_line z' l₁ → z' = z) ∧ -- ... in exactly one point.
  (∃ z ∈ t.points, Complex.abs (z-z₂) = dist_point_line z l₂ ∧ -- t is intersecting the parabola of z₂ and l₂ ...
  ∀ z' ∈ t.points, Complex.abs (z'-z₂) = dist_point_line z' l₂ → z' = z) -- ... in exactly one point.
  }


-- ToDo: Maybe add axiom O7? It's not necessary, I think, but surely nice to have...


/- *Let's define the closure of M under iteratively intersecting lines generated by M and the origami numbers.* -/

/-- All the lines generated by using the axioms on elements of M and L.-/
def generate_lines (M : Set ℂ) (L : Set line) : Set line := {l : line |
  (∃ z₁ ∈ M, ∃ z₂ ∈ M, ∃ h : z₁ ≠ z₂, l.eq (O1 z₁ z₂ h))
  ∨
  (∃ z₁ ∈ M, ∃ z₂ ∈ M, ∃ h : z₁ ≠ z₂, l.eq (O2 z₁ z₂ h))
  ∨
  (∃ l₁ ∈ L, ∃ l₂ ∈ L, l.eq (O3 l₁ l₂))
  ∨
  (∃ l₁ ∈ L, ∃ l₂ ∈ L, l.eq (O3' l₁ l₂))
  ∨
  (∃ z₁ ∈ M, ∃ l₁ ∈ L, l.eq (O4 z₁ l₁))
  ∨
  (∃ z₁ ∈ M, ∃ z₂ ∈ M, ∃ h : z₁ ≠ z₂, ∃ l₁ ∈ L, ∃ l' ∈ O5 z₁ z₂ h l₁, l.eq l')
  ∨
  (∃ z₁ ∈ M, ∃ z₂ ∈ M, ∃ h : z₁ ≠ z₂, ∃ l₁ ∈ L, ∃ l₂ ∈ L, ∃ l' ∈ O6 z₁ z₂ h l₁ l₂, l.eq l')
  --∨
  --(∃ z₁ ∈ M, ∃ z₂ ∈ M, z₁ ≠ z₂ ∧ ∃ l₁ ∈ L, ∃ l₂ ∈ L, ∃ l' ∈ O7 z₁ z₂ (by sorry) l₁ l₂, l.eq l')
  }

/-- All the intersection points of elements of L.-/
def generate_points (L : Set line) : Set ℂ :=
  {z : ℂ | ∃ l₁ ∈ L, ∃ l₂ ∈ L, ∃ h : ¬AreParallel l₁ l₂, z = Isect l₁ l₂ h}

/-- Iteratively generating and intersecting lines, given a starting set of points and lines.-/
@[simp] def 𝕆ₙ (𝕆₀ : Set ℂ × Set line := ({0,1},∅)) : ℕ → Set ℂ × Set line
  | 0 => 𝕆₀
  | (Nat.succ n) => (
      (𝕆ₙ 𝕆₀ n).1 ∪ generate_points (𝕆ₙ 𝕆₀ n).2,
      {l | ∃ l₁ ∈ (𝕆ₙ 𝕆₀ n).2, l.eq l₁} ∪ generate_lines (𝕆ₙ 𝕆₀ n).1 (𝕆ₙ 𝕆₀ n).2)

@[simp] def 𝕆ₙ.points (n : ℕ) (M₀ : Set ℂ := {0,1}) (L₀ : Set line := ∅) : Set ℂ :=
  (𝕆ₙ (M₀, L₀) n).1
@[simp] def 𝕆ₙ.lines (n : ℕ) (M₀ : Set ℂ := {0,1}) (L₀ : Set line := ∅) : Set line :=
  (𝕆ₙ (M₀, L₀) n).2

/-- The limes of 𝕆₀ ⊆ 𝕆₁ ⊆ 𝕆₂ ⊆ ...-/
@[simp] def 𝕆_infty (M₀ : Set ℂ := {0,1}) (L₀ : Set line := ∅) : Set ℂ :=
  ⋃ (n : ℕ), 𝕆ₙ.points n M₀ L₀
@[simp] def 𝕆_infty.lines (M₀ : Set ℂ := {0,1}) (L₀ : Set line := ∅) : Set line :=
  ⋃ (n : ℕ), 𝕆ₙ.lines n M₀ L₀

/-- The classical origami numbers.-/
def 𝕆 : Set ℂ := 𝕆_infty
/-- The lines generated by the classical origami numbers.-/
def 𝕆.lines : Set line := 𝕆_infty.lines






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
      left; use l; simp; exact im h' hl
    · have : n = m + 1 := by linarith
      rw [this]

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
lemma O4_perpendicular {l : line} {z : ℂ} :
  (l.vec * conj (O4 z l).vec).re = 0 := by
    simp [O4, line.vec, div_self vec_well_defined]
    ring

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

lemma Complex.sq_abs_eq {z : ℂ} : (Complex.abs z)^2 = (z.re : ℂ)^2 + (z.im : ℂ)^2 := by
  norm_cast
  simp [← Complex.sq_abs_sub_sq_im]
lemma Complex.sq_abs_eq_in_ℝ {z : ℂ} : (Complex.abs z)^2 = (z.re)^2 + (z.im)^2 := by
  simp [← Complex.sq_abs_sub_sq_im]





-- **Two Folding Lemmata**

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
      field_simp
      simp [mul_div_assoc, sub_eq_add_neg, ← mul_assoc, ← neg_div, neg_sub]
      rfl

/-- Given a point z and a line l, fold a line parallel to l that goes through z.-/
lemma E1_in_𝕆' (z : ℂ) (l : line) (hz : z ∈ 𝕆) (hl : l ∈ 𝕆.lines) :
  ∃ l' ∈ 𝕆.lines, l'.z₁ = z ∧ l'.z₂ = z - l.vec := by
    use ⟨z,z - l.vec,(by simp [sub_eq_neg_add, vec_ne_zero l])⟩
    constructor
    · exact E1_in_𝕆 z l hz hl
    · simp

lemma E1_in_𝕆'' (z : ℂ) (l : line) (hz : z ∈ 𝕆) (hl : l ∈ 𝕆.lines) :
  (E1 z l).z₁ = z ∧ (E1 z l).z₂ = z - l.vec ∧ AreParallel l (E1 z l):= by
    unfold E1
    constructor
    · simp
    · constructor
      · simp
      · unfold AreParallel
        unfold line.vec
        simp
        right
        simp_rw [neg_div', neg_neg]
        rw[← line.vec, div_self]
        rw[div_one]
        have := l.z₁_neq_z₂
        simp
        exact this.symm

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
    ring_nf; field_simp
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
    field_simp [add_sub_assoc]
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
    have : (Complex.abs z : ℂ) ≠ 0 := by norm_cast; exact (AbsoluteValue.ne_zero_iff Complex.abs).mpr z_ne_zero
    simp [line.vec, hl₂_z₁, hl₂_z₂, div_self this, neg_div]

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
    have : (Complex.abs z : ℂ) ≠ 0 := by norm_cast; exact (AbsoluteValue.ne_zero_iff Complex.abs).mpr z_ne_zero
    simp [line.vec, hl₂_z₁, hl₂_z₂, div_self this, neg_div]

  apply in_𝕆_if_eq (E2 0 l₂)
  · exact E2_in_𝕆 0 l₂ zero_in_𝕆 hl₂
  simp [E2, hl₂_z₁, hl₂_vec, z_ne_zero]
  ring_nf

lemma 𝕆_add_multiples {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ 𝕆) (hz₂ : z₂ ∈ 𝕆) (h_multiple : ∃ a : ℝ, z₁ = a * z₂) : z₁ + z₂ ∈ 𝕆 := by
  -- Here is the proof why we can assume w.l.o.g. that |z₁| < |z₂| holds.
  by_cases h_abs_ne : z₁ = z₂ ∨ z₁ = -z₂
  · -- The case that z₁ = ±z₂,
    -- therefore their sum equals 0 or 2 * z₁. Apply zero_in_𝕆 or 𝕆_double.
    obtain ⟨a,ha⟩ := h_multiple
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
    by_cases hz₁_ne_zero : z₁ = 0; simp [hz₁_ne_zero, hz₂]
    by_cases hz₂_ne_zero : z₂ = 0; simp [hz₂_ne_zero, hz₁]
    by_cases hz₁_ne_h₂ : z₁ = z₂; rw [← hz₁_ne_h₂,← two_mul]; apply 𝕆_double hz₁
    push_neg at hz₁_ne_zero hz₂_ne_zero
    obtain ⟨a,ha⟩ := h_multiple

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
    field_simp
    have h1 : (Complex.abs z₁ : ℂ) ≠ 0 := by norm_cast; exact (AbsoluteValue.ne_zero_iff Complex.abs).mpr hz₁_ne_zero
    have h2 : (Complex.abs z₂ : ℂ) ≠ 0 := by norm_cast; exact (AbsoluteValue.ne_zero_iff Complex.abs).mpr hz₂_ne_zero
    rw [mul_assoc (Complex.abs z₂ : ℂ), mul_comm ((-((z₂.re : ℂ) * z₁.im) + (z₂.im : ℂ) * z₁.re))]
    rw [mul_comm (Complex.abs z₂ : ℂ),  ← mul_assoc (Complex.abs z₂ : ℂ), ← mul_assoc, mul_comm, mul_div_assoc, ← div_div, ← div_div, mul_div_assoc, div_self h2, mul_one]
    rw [mul_div_assoc, div_self h1, mul_one]
    ring_nf
    simp
    symm
    field_simp
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

theorem 𝕆_inv {z : ℂ} (hz : z ∈ 𝕆) : z⁻¹ ∈ 𝕆 := by
  -- W.l.o.g., suppose that z ≠ 0.
  by_cases hz_ne_zero : z = 0
  · simp [hz_ne_zero, zero_in_𝕆]
  sorry

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
  simp[← neg_div, div_self this, ← neg_mul]
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
      := by ring;

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

/-
lemma 𝕆_real {a : ℝ} : (a : ℂ) ∈ 𝕆 := by
  rw [← mul_one a]
  push_cast
  apply 𝕆_real_mul_real (Complex.ofReal_im a) (Complex.ofReal_im 1) (sorry) one_in_𝕆
-/

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
  have : (Complex.abs z : ℂ) ≠ 0 := by norm_cast; exact (AbsoluteValue.ne_zero_iff Complex.abs).mpr hz_ne_zero
  simp [E2, hl₃_z₁, hl₃_z₂, line.vec, div_self this]
  field_simp
  simp [← neg_mul, ← add_mul, ← mul_div, mul_assoc, ← div_div, div_self this]
  ring_nf
  field_simp
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
          := by simp [div_self, this]
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


-- **ℚ ⊆ 𝕆**

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

lemma rat_in_𝕆 : ∀ r : ℚ, (r : ℂ) ∈ 𝕆 := by 
  intro r
  have : (r : ℂ) = r.num / r.den := by norm_cast; symm; exact Rat.divInt_self r
  simp_rw [this]
  apply 𝕆_div
  · apply int_in_𝕆
  · apply nat_in_𝕆


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
    simp [O5, reAxis, O1, z₁]
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
    
lemma half_angle {z : ℂ} (hz : z ∈ 𝕆) : Complex.exp (z.arg/2 * Complex.I) ∈ 𝕆 := by 
  by_cases z_ne_zero : z = 0
  · simp [z_ne_zero, one_in_𝕆]
  
  let l₁ := O1 z 0 z_ne_zero
  have hl₁ : l₁ ∈ 𝕆.lines := O1_in_𝕆 hz zero_in_𝕆
  
  by_cases l₁_reAxis_not_parallel : AreParallel l₁ reAxis
  · sorry
  
  let l₂ := O3 l₁ reAxis -- or O3' ????
  have hl₂ : l₂ ∈ 𝕆.lines := O3_in_𝕆 hl₁ reAxis_in_𝕆
  have l₁_l₂_not_parallel : ¬AreParallel l₁ l₂ := by 
    simp [AreParallel]
    sorry
  let z₁ := Isect l₁ l₂ l₁_l₂_not_parallel
  apply in_𝕆_if_eq (z₁ / Complex.abs z₁)
  · unfold z₁
    apply 𝕆_div
    · exact Isect_in_𝕆 hl₁ hl₂
    · exact 𝕆_abs (Isect_in_𝕆 hl₁ hl₂)
  · simp [z₁, Isect, l₁_l₂_not_parallel]
    simp [l₂, O3]
    simp [reAxis, line.vec, Isect, O1]
    simp [l₁, O1]
    sorry

theorem 𝕆_square_roots {z : ℂ} (hz : z ∈ 𝕆) : ∃ z' ∈ 𝕆, z = z' * z' := by 
  let z_pol := Complex.polarCoord z
  use Complex.polarCoord.symm (√(z_pol.1), z_pol.2 / 2)
  simp [Complex.polarCoord_symm_apply, z_pol, Complex.polarCoord_apply]
  constructor
  · apply 𝕆_mul
    · by_cases h : Complex.abs z = 0 
      · simp [h, zero_in_𝕆]
      · apply 𝕆_square_roots_pos_real
        · simp [(AbsoluteValue.ne_zero_iff Complex.abs).mp h, AbsoluteValue.nonneg Complex.abs z]
        · exact 𝕆_abs hz
    · simp [Complex.cos_add_sin_I]
      exact half_angle hz
  · rw [Complex.cos_add_sin_I]
    ring_nf
    norm_cast
    rw [Real.sq_sqrt (AbsoluteValue.nonneg Complex.abs z)]
    rw [← Complex.exp_nat_mul (z.arg * Complex.I * (1/2)) 2]
    simp [← mul_assoc, mul_comm]
    rw [mul_comm, mul_comm Complex.I]
    exact Eq.symm (Complex.abs_mul_exp_arg_mul_I z)
    

end square_root

section cube_root
#check Complex.sin_three_mul
theorem 𝕆_cube_roots {z : ℂ} (hz : z ∈ 𝕆) : ∃ z' ∈ 𝕆, z = z' * z' * z' := by sorry
end cube_root
