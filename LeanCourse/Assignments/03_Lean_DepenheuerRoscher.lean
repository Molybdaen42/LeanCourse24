/-

 Nora Depenheuer & Joachim Roscher

-/

--import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
open Real Function Set Nat

/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 3, sections 2, 3, 5, 6.
  Read chapter 4, section 1.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 29.10.2023.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/

def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

/-! # Exercises to hand-in. -/
/- Prove the following with basic tactics, without using `tauto` or lemmas from Mathlib. -/
lemma exists_distributes_over_or {α : Type*} {p q : α → Prop} :
    (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by {
  constructor
  · intro h
    obtain⟨x₀,hx⟩ := h
    obtain hp|hq := hx
    · left
      use x₀
    · right
      use x₀
  · intro h
    obtain hp|hq := h
    · obtain⟨x₀, hx⟩ := hp
      use x₀
      left
      exact hx
    · obtain⟨x₀, hx⟩ := hq
      use x₀
      right
      exact hx
  }

section Surjectivity

/- Lean's mathematical library knows what a surjective function is,
but let's define it here ourselves and prove some things about it. -/
def SurjectiveFunction (f : ℝ → ℝ) : Prop :=
  ∀ (y : ℝ), ∃ (x : ℝ), f x = y

variable {f g : ℝ → ℝ} {x : ℝ}

/- `rfl` or `simp` can compute the following.
`simp` is a very useful tactic that can simplify many expressions. -/
example : (g ∘ f) x = g (f x) := by simp

lemma surjective_composition (hf : SurjectiveFunction f) :
    SurjectiveFunction (g ∘ f) ↔ SurjectiveFunction g := by {
  constructor
  · intro h1
    unfold SurjectiveFunction at h1
    intro y
    obtain⟨x₀, hx⟩ := h1 y
    simp at hx
    use f x₀
  · intro h2
    unfold SurjectiveFunction at h2
    intro y
    obtain⟨x₀, hy⟩ := h2 y
    obtain⟨x₁ , hx⟩ := hf x₀
    simp
    use x₁
    rw[hx]
    exact hy
  }

/- When composing a surjective function by a linear function
to the left and the right, the result will still be a
surjective function. The `ring` tactic will be very useful here! -/
lemma surjective_linear (hf : SurjectiveFunction f) :
    SurjectiveFunction (fun x ↦ 2 * f (3 * (x + 4)) + 1) := by {
  unfold SurjectiveFunction at hf
  intro y
  obtain⟨x₀ , hx⟩ := hf ((y-1)/2)
  use ((x₀ /3)-4)
  simp
  ring
  rw[hx]
  ring
  }


/- Let's prove Cantor's theorem:
there is no surjective function from any set to its power set.
Hint: use `let R := {x | x ∉ f x}` to consider the set `R` of elements `x`
that are not in `f x`
-/
lemma exercise_cantor (α : Type*) (f : α → Set α) : ¬ Surjective f := by {
  -- let's define a useful set
  let R := {x | x ∉ f x}

  -- unfold stuff
  unfold Surjective

  -- it will be a proof by contradiction
  by_contra f_surj

  -- R would have a preimage under f
  obtain ⟨a,h_fa_eq_R⟩ := f_surj R

  -- we'll prove that a ∈ R iff a ∉ R
  by_cases ha: a ∈ R
  · -- case a ∈ R
    have h1 : a ∉ R := by exact Eq.mpr_not (congrFun (id (Eq.symm h_fa_eq_R)) a) ha
    contradiction
  · -- case a ∉ R
    have h1 : a ∈ R := by exact Eq.mpr_not (congrFun h_fa_eq_R a) ha
    contradiction
  }

end Surjectivity

/- Prove that the sum of two converging sequences converges. -/
lemma sequentialLimit_add {s t : ℕ → ℝ} {a b : ℝ}
      (hs : SequentialLimit s a) (ht : SequentialLimit t b) :
    SequentialLimit (fun n ↦ s n + t n) (a + b) := by {
  unfold SequentialLimit
  unfold SequentialLimit at hs ht
  -- let ε > 0
  intro ε hε

  -- plug ε/2 in hs and ht
  have hε2 : ε/2 > 0 := by linarith
  obtain ⟨Ns, hNs⟩ := hs (ε/2) hε2
  obtain ⟨Nt, hNt⟩ := ht (ε/2) hε2

  -- we could also use the maximum of Ns and Nt
  use (Ns + Nt)

  -- ∀ n ≥ Ns + Nt
  intro n hn
  have hns : n ≥ Ns := by linarith
  have hnt : n ≥ Nt := by linarith

  -- inequalities of hs and ht with ε/2
  obtain hs_final := hNs n hns
  obtain ht_final := hNt n hnt

  -- final calculation
  simp
  calc
    |s n + t n - (a + b)| = |(s n - a) + (t n - b)| := by ring
                        _ ≤ |s n - a| + |t n - b|   := by exact abs_add_le (s n - a) (t n - b)
                        _ < ε/2 + ε/2               := by linarith
                        _ = ε                       := by linarith
  }

/- It may be useful to case split on whether `c = 0` is true. -/
lemma sequentialLimit_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (hs : SequentialLimit s a) :
    SequentialLimit (fun n ↦ c * s n) (c * a) := by {
  unfold SequentialLimit
  unfold SequentialLimit at hs
  -- let ε > 0
  intro ε hε

  -- prove that ε / (|c| + 1) is positive
  have := by exact abs_nonneg c -- |c| ≥ 0
  have hc : |c|+1 > 0 := by linarith

  -- plug ε / (|c| + 1) in hs and get Ns such that hNs
  obtain ⟨Ns, hNs⟩ := hs (ε / (|c| + 1)) (div_pos hε hc)

  use Ns
  intro n hn
  simp

  -- making some necessary statements for the following calculation
  have hc_nonneg : |c| + 1 ≠ 0 := by linarith
  have hc_equal1 : (|c| + 1) / (|c| + 1) = 1 := by exact (div_eq_one_iff_eq hc_nonneg).mpr rfl
  have := by exact abs_nonneg (s n - a)

  -- final calculation
  calc
    |c * s n - c * a| = |c * (s n - a)|             := by ring
                    _ = |c| * |s n - a|             := by exact abs_mul c (s n - a)
                    _ ≤ (|c| + 1) * |s n - a|       := by linarith
                    _ < (|c| + 1) * (ε / (|c| + 1)) := by exact (mul_lt_mul_left hc).mpr (hNs n hn)
                    _ = ε * ((|c| + 1) / (|c| + 1)) := by ring
                    _ = ε * 1                       := by rw[hc_equal1]
                    _ = ε                           := by ring
  }




section Growth

variable {s t : ℕ → ℕ} {k : ℕ}

/- `simp` can help you simplify expressions like the following. -/
example : (fun n ↦ n * s n) k = k * s k := by simp
example (a b c : ℕ) : c ≥ max a b ↔ c ≥ a ∧ c ≥ b := by simp

/- Given two sequences of natural numbers `s` and `t`.
We say that `s` eventually grows faster than `t` if for all `k : ℕ`,
`s_n` will be at least as large as `k * t_n` for large enough `n`. -/
def EventuallyGrowsFaster (s t : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, k * t n ≤ s n

/- show that `n * s n` grows (eventually) faster than `s n`. -/
lemma eventuallyGrowsFaster_mul_left :
    EventuallyGrowsFaster (fun n ↦ n * s n) s := by {
  unfold EventuallyGrowsFaster
  simp
  intro k
  use k
  intro n hn
  exact Nat.mul_le_mul_right (s n) hn
  }

/- Show that if `sᵢ` grows eventually faster than `tᵢ` then
`s₁ + s₂` grows eventually faster than `t₁ + t₂`. -/
lemma eventuallyGrowsFaster_add {s₁ s₂ t₁ t₂ : ℕ → ℕ}
    (h₁ : EventuallyGrowsFaster s₁ t₁) (h₂ : EventuallyGrowsFaster s₂ t₂) :
    EventuallyGrowsFaster (s₁ + s₂) (t₁ + t₂) := by {
  -- unfold and simplify things
  unfold EventuallyGrowsFaster
  unfold EventuallyGrowsFaster at h₁ h₂
  simp

  -- ∀ k
  intro k

  -- plug k in h₁ and h₂ and obtain the N-s
  obtain ⟨N₁, hN₁⟩ := h₁ k
  obtain ⟨N₂, hN₂⟩ := h₂ k

  -- use N = max N₁ N₂
  let N := max N₁ N₂
  use N

  -- ∀ n ≥ N
  intro n hn
  specialize hN₁ n
  specialize hN₂ n

  -- check that n ≥ N₁ and n ≥ N₂
  have hn₁ : n ≥ N₁ := by exact le_of_max_le_left hn
  have hn₂ : n ≥ N₂ := by exact le_of_max_le_right hn

  -- final calculation
  calc
    k * (t₁ n + t₂ n) = k * t₁ n + k * t₂ n := by ring
                    _ ≤ s₁ n + k * t₂ n := by exact Nat.add_le_add_right (hN₁ hn₁) (k * t₂ n)
                    _ ≤ s₁ n + s₂ n := by exact Nat.add_le_add_left (hN₂ hn₂) (s₁ n)
  }

/- Find a positive function that grows faster than itself when shifted by one. -/
lemma eventuallyGrowsFaster_shift : ∃ (s : ℕ → ℕ),
    EventuallyGrowsFaster (fun n ↦ s (n+1)) s ∧ ∀ n, s n ≠ 0 := by {
  -- unfold stuff
  unfold EventuallyGrowsFaster

  -- use s = id
  use fun n ↦ n^n

  -- we have two things to prove
  constructor
  · intro k

    -- use N = k
    use k
    intro n hn
    simp

    -- we will need this trivial fact in the calculation
    have h_n_succ_is_bigger : n ≤ n+1 := by exact Nat.le_add_right n 1

    -- final calculation
    calc
      k * n ^ n ≤ n * n ^ n     := by exact Nat.mul_le_mul_right (n ^ n) hn
              _ = n ^ (n+1)     := by exact Eq.symm Nat.pow_succ'
              _ ≤ (n+1) ^ (n+1) := by exact pow_le_pow_of_le_left h_n_succ_is_bigger (n + 1)

  · simp -- n^n is never 0
  }

end Growth
