import LeanCourse.Project.defs

open Construction

def StartSet : Set ℂ := {0, 1}
def l1 : line := ⟨0, 1, zero_ne_one⟩
def l2 : line := O1 1 0 zero_ne_one.symm
def l3 : line := O1 0 Complex.I Complex.I_ne_zero.symm
--#eval l1.points
#eval l1.z₂

example : l1.points = l2.points := by
  simp
  ext x
  simp
  constructor
  · intro ⟨t, ht⟩
    use 1-t
    simp
    rw [add_comm]
    unfold line.z₁
    sorry
  · sorry

example : 2 ∈ l1.points := by
  simp
  use -1
  norm_num
  sorry

---------------------------------------

structure line2 where
  (z₁ z₂ : ℂ)

@[simp] def line2.points (l : line2) : Set ℂ := {(t : ℂ) * l.z₁ + (1-t) * l.z₂ | (t : ℝ)}

def l1' : line2 := ⟨0, 1⟩
def l2' : line2 := ⟨1, 0⟩

example : l1'.points = l2'.points := by
  simp
  ext x
  simp
  constructor
  · intro ⟨t, ht⟩
    use 1-t
    simp
    rw [add_comm]
    unfold line2.z₁
    sorry
  · sorry
