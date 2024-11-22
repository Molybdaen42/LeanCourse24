import LeanCourse.Project.defs
open Classical
open Construction

def StartSet : Set ℂ := {0, 1}
def l1 : line := ⟨0, 1, zero_ne_one⟩
def l2 : line := O1 1 0 zero_ne_one.symm
def l3 : line := O1 0 Complex.I Complex.I_ne_zero.symm
--#eval l1.points
#eval l1.z₂

example : l1.points = l2.points := by
  simp [l1, l2]
  ext x
  simp
  constructor
  · intro ⟨t, ht⟩
    use 1-t
    simp [← ht]

    rw [add_comm]

    sorry
  · sorry

example : 2 ∈ l1.points := by
  simp
  use -1
  norm_num
  sorry

def generate_lines (M : Set ℂ) (L : Set line) : Set line := {l : line |
  ∃ z₁ ∈ M, ∃ z₂ ∈ M, z₁ ≠ z₂ ∧ (
  l = O1 z₁ z₂ (by sorry)
  ∨
  l = O2 z₁ z₂ (by sorry)
  ∨
  ∃ l₁ ∈ L, ∃ l₂ ∈ L, (
  l = O3 l₁ l₂
  ∨
  l = O3' l₁ l₂
  ∨
  l = O4 z₁ l₁
  ∨
  l ∈ O5 z₁ z₂ (by sorry) l₁
  ∨
  l ∈ O6 z₁ z₂ (by sorry) l₁ l₂
  --∨
  --l ∈ O7 z₁ z₂ l₁ l₂
  ))}

def generate_points (L : Set line) : Set ℂ := {z : ℂ | ∃ l₁ ∈ L, ∃ l₂ ∈ L, ¬AreParallel l₁ l₂ ∧ z = Isect l₁ l₂ (by sorry)}

def M₀ : Set ℂ := {0,1}
def L₀ : Set line := ∅

def L₁ : Set line := L₀ ∪ generate_lines M₀ L₀
def M₁ : Set ℂ := M₀ ∪ generate_points L₁

def L₂ : Set line := L₁ ∪ generate_lines M₁ L₁
def M₂ : Set ℂ := M₁ ∪ generate_points L₂

def L₃ : Set line := L₂ ∪ generate_lines M₂ L₂
def M₃ : Set ℂ := M₂ ∪ generate_points L₃

-- We want to prove that i is in M₂
lemma i_in_O : Complex.I ∈ M₃ := by
  -- first define all necessary lines and points
  let reAxis : line := O1 0 1 (zero_ne_one)
  let imAxis : line := O4 0 reAxis
  let l₁ : line := O4 1 reAxis
  let l₂ : line := O3 reAxis l₁

  -- then show that they lie in L₁ or L₂
  have h1 : reAxis ∈ L₁ := by
    --it's generated from M₀ and L₀
    right
    -- Want to use O1(0, 1)
    use 0
    -- 0 lies in M₀
    constructor; unfold M₀; simp
    -- Still want to use O1(0, 1)
    use 1
    -- 1 lies in M₀
    constructor; unfold M₀; simp
    -- the rest follows
    simp
  --have h2 : reAxis ∈ L₂ := by left; exact h1
  have h3 : imAxis ∈ L₂ := by sorry
  have h4 : l₁ ∈ L₂ := by sorry
  have h5 : l₂ ∈ L₃ := by sorry

  /- -- Now put it all together
  unfold M₂ generate_points
  right; simp
  use l₂
  constructor
  · unfold L₂ generate_lines
    simp
    sorry
  · use imAxis
    constructor
    · sorry
    · sorry -/
  sorry
--intersection points of {(Linien aus M) ∪ (alles aus O1) ∪ (alles aus O2)...}
