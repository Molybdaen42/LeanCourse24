import Mathlib.Data.Complex.Basic
import Mathlib.Order.Basic
import Mathlib.Geometry.Euclidean.Sphere.Basic

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
  (z₁ z₂ : ℂ) (z₁_ne_z₂ : z₁ ≠ z₂)

/-- The points of a line given by two different points z₁ and z₂ are
 the linear combinations of these two points.-/
@[simp] def line.points (l : line) : Set ℂ := {(t : ℂ) * l.z₁ + (1-t) * l.z₂ | (t : ℝ)}

/-- A normalised direction vector of the line.-/
--@[simp]
noncomputable def line.vec (l : line) : ℂ := (l.z₂ - l.z₁) / (Complex.abs (l.z₂ - l.z₁))

/-- The denominator of line.vec is never zero. -/
@[simp] lemma vec_well_defined {l : line} : Complex.abs (l.z₂ - l.z₁) ≠ 0 := by simp [l.z₁_ne_z₂.symm]

/-- The direction vector l.vec is never zero.-/
lemma vec_ne_zero (l : line) : l.vec ≠ 0 := by
  unfold line.vec
  simp
  constructor
  · apply sub_ne_zero_of_ne
    exact l.z₁_ne_z₂.symm
  · exact l.z₁_ne_z₂.symm

/-- The direction vector is of length one.-/
lemma vec_abs_one (l : line) : Complex.abs l.vec = 1 := by
  simp [line.vec, map_div₀, Complex.abs_ofReal, Complex.abs_abs, div_self vec_well_defined]

/-- The term z₂ - z₁ is never zero.-/
lemma diff_ne_zero (l : line) : l.z₂ - l.z₁ ≠ 0 := by
  exact sub_ne_zero_of_ne l.z₁_ne_z₂.symm
/-- The term z₂ - z₁ is never zero.-/
lemma diff_ne_zero' (l : line) : l.z₁ - l.z₂ ≠ 0 := by
  exact sub_ne_zero_of_ne l.z₁_ne_z₂

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
  Using the first one will satisfy our needs while the other one requires equal generating points.-/
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

lemma line_eq_if_switched_points (l : line) : l.eq ⟨l.z₂, l.z₁, l.z₁_ne_z₂.symm⟩ := by
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
          have := l₁.z₁_ne_z₂
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
    exact Complex.ofReal_ne_zero.mpr vec_well_defined
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

--ToDo: necessary?
--def sProd : ℂ × ℂ → ℂ := fun (z₁, z₂) ↦ (z₁ * conj z₂).re
--def orth_sProd : ℂ × ℂ → ℂ := fun (z₁, z₂) ↦ (z₁ * conj z₂).im


/-- Computes the intersection point of l₁ and l₂.-/
-- The dot product of vectors v^⊥ and u is
-- the imaginary part of complex multiplication of v with the complex conjugate of u
noncomputable def Isect (l₁ l₂ : line) (h : ¬AreParallel l₁ l₂) : ℂ :=
  l₁.z₁ - (l₂.vec * conj (l₁.z₁ - l₂.z₁)).im / (l₂.vec * conj l₁.vec).im * l₁.vec
-- Is (h : ¬AreParallel l₁ l₂) a necessary/useful condition?
-- Maybe not, since /0 = 0 and


/- **The Axioms of origami number construction** -/

-- First example
--/-- The set of intersection points of lines generated by M in only one interation.-/
--def intersec_of_two_lines_gen_by (M:Set ℂ): Set ℂ := { z : ℂ | ∃ l₁ ∈ Lines_gen_by M, ∃ l₂ ∈ Lines_gen_by M, l₁ ≠ l₂ ∧ z ∈ l₁.points ∩ l₂.points}

/-- Given two different points, we can fold a line that goes through both of them.-/
def O1 (z₁ z₂ : ℂ) (h : z₁ ≠ z₂) : line := {z₁ := z₁, z₂ := z₂, z₁_ne_z₂ := h : line}

/-- Given two different points z₁ and z₂, we can fold z₁ onto z₂
(i.e. find the perpendicular bisector of segment z₁z₂).-/
noncomputable def O2 (z₁ z₂ : ℂ) (h : z₁ ≠ z₂) : line where
  z₁ := (z₁+z₂)/2                      -- the midpoint of z₁ and z₂
  z₂ := (z₁+z₂)/2 + Complex.I*(z₂-z₁) -- turns the vector z₂-z₁ by 90° and adds it to the midpoint
  z₁_ne_z₂ := by
    simp [div_add', eq_div_iff]
    exact sub_ne_zero_of_ne (id (Ne.symm h))

/-- Given two lines l₁ and l₂, we can fold l₁ onto l₂ (i.e. bisect the angle
between them). [Attention: There are two possibilities for the fold, the two of them being orthogonal to each other!]-/
noncomputable def O3 (l₁ l₂ : line) : line := if h : AreParallel l₁ l₂ then {
  z₁ := (l₁.z₁ + l₂.z₁)/2
  z₂ := (l₁.z₁ + l₂.z₂)/2
  z₁_ne_z₂ := by simp [eq_div_iff, IsUnit.div_mul_cancel,l₂.z₁_ne_z₂]
} else {
  z₁ := Isect l₁ l₂ h
  z₂ := Isect l₁ l₂ h + l₁.vec + l₂.vec -- Be attentive to the signs!
  z₁_ne_z₂ := by
    simp [add_assoc]
    rw [← sub_neg_eq_add]
    simp [AreParallel] at h
    exact sub_ne_zero_of_ne h.2
}

/-- Given two lines l₁ and l₂, we can fold l₁ onto l₂ (i.e. bisect the angle
between them). [Attention: There are two possibilities for the fold, the two of them being orthogonal to each other!]-/
noncomputable def O3' (l₁ l₂ : line) : line := if h : AreParallel l₁ l₂ then {
  z₁ := (l₁.z₁ + l₂.z₁)/2
  z₂ := (l₁.z₁ + l₂.z₂)/2
  z₁_ne_z₂ := by simp [eq_div_iff, IsUnit.div_mul_cancel,l₂.z₁_ne_z₂]
} else {
  z₁ := Isect l₁ l₂ h
  z₂ := Isect l₁ l₂ h + l₁.vec - l₂.vec -- Be attentive to the signs!
  z₁_ne_z₂ := by
    simp [add_sub_assoc]
    simp [AreParallel] at h
    exact sub_ne_zero_of_ne h.1
}


/-- Given a point z and a line l, we can fold a line perpendicular to l that
goes through z.-/
noncomputable def O4 (z : ℂ) (l : line) : line where
  z₁ := z
  z₂ := z + Complex.I*l.vec
  z₁_ne_z₂ := by simp; exact vec_ne_zero l


/-- Given two points z1 and z2 and a line l, we can fold z1 onto l with a
line that goes through z2. There are 0, 1 or 2 solutions possible.-/
noncomputable def O5 (z₁ z₂ : ℂ) (h : z₁ ≠ z₂) (l : line) : Set line :=
  {l' : line | l'.z₁ = z₂ ∧
  2 * l'.z₂ - z₁ ∈ l.points ∧ Complex.abs (2 * l'.z₂ - z₁ - z₂) = Complex.abs (z₁-z₂)}

-- ToDo: lemma O5_has_a_solution {z₁ z₂ : ℂ} (h : ...) : Nonempty O5 ... := by ...

/--Given two points z1 and z2 and two lines l1 and l2, we can fold z1 onto
l1 and z2 onto l2 with a single line.-/
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


/- **Let's define the closure of M under iteratively intersecting lines generated by M and the origami numbers.** -/

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
@[simp] def 𝕆ₙ : ℕ → Set ℂ × Set line
  | 0 => ({0,1}, ∅)
  | (Nat.succ n) => (
      (𝕆ₙ n).1 ∪ generate_points (𝕆ₙ n).2,
      {l | ∃ l₁ ∈ (𝕆ₙ n).2, l.eq l₁} ∪ generate_lines (𝕆ₙ n).1 (𝕆ₙ n).2)

@[simp] def 𝕆ₙ.points (n : ℕ) : Set ℂ := (𝕆ₙ n).1
@[simp] def 𝕆ₙ.lines (n : ℕ) : Set line := (𝕆ₙ n).2

/-- The classical origami numbers.-/
def 𝕆 : Set ℂ := ⋃ (n : ℕ), 𝕆ₙ.points n
/-- The lines generated by the classical origami numbers.-/
def 𝕆.lines : Set line := ⋃ (n : ℕ), 𝕆ₙ.lines n
