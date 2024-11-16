import LeanCourse.Common
import Init.Data.Queue
import Mathlib.Data.Complex.Exponential
open Real

/-! # Exercises to hand-in. -/

/- Prove this using a calculation. -/
lemma exercise_calc_real {t : ℝ} (ht : t ≥ 10) : t ^ 2 - 3 * t - 17 ≥ 5 := by {
  have h1 : t-6 ≥ 0 := by linarith
  have h2 : t+2 ≥ 0 := by linarith
  have h3 : (t-6)*(t+2) ≥ 0 := by exact mul_nonneg h1 h2
  calc
    t^2 - 3*t - 17 = t^2 - 4*t - 12 + t - 5 := by ring
                 _ = (t-6)*(t+2) + t - 5    := by ring
                 _ ≥ (t-6)*(t+2) + 5        := by linarith
                 _ ≥ 5                      := by linarith
  }

/- Prove this using a calculation.
The arguments {R : Type*} [CommRing R] {t : R} mean
"let t be an element of an arbitrary commutative ring R." -/
lemma exercise_calc_ring {R : Type*} [CommRing R] {t : R}
    (ht : t ^ 2 - 4 = 0) :
    t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 = 10 * t + 2 := by {
  calc
    t^4 + 3*t^3 - 3*t^2 - 2*t - 2 = (t^2-4)*(t^2 + 3*t + 1) + 10*t+2 := by ring
                                _ = 0*(t^2+3*t+1) + 10*t+2           := by rw[ht]
                                _ = 10*t+2                           := by ring
  }

/-- Prove this using a calculation. -/
lemma exercise_square {m n k : ℤ} (h : m ^ 2 + n ≤ 2) : n + 1 ≤ 3 + k ^ 2 := by {
  calc
    n + 1 ≤ 3 + n - 2         := by linarith
        _ ≤ 3 + n - (m^2 + n) := by linarith
        _ ≤ 3 - m^2           := by linarith
        _ ≤ 3 - 0             := by gcongr; exact sq_nonneg m
        _ ≤ 3 + 0             := by linarith
        _ ≤ 3 + k^2           := by gcongr; exact sq_nonneg k
  }



section Min
variable (a b c : ℝ)

/- The following theorems characterize min.
Let's this characterization it to prove that min is commutative and associative.
Don't use other lemmas about min from Mathlib! -/
#check (min : ℝ → ℝ → ℝ)
#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

lemma exercise_min_comm : min a b = min b a := by {
  have h11 : min a b ≤ b := by exact min_le_right a b
  have h12 : min a b ≤ a := by exact min_le_left a b
  have h1 : min a b ≤ min b a := by exact le_min h11 h12
  have h21 : min b a ≤ a := by exact min_le_right b a
  have h22 : min b a ≤ b := by exact min_le_left b a
  have h2 : min a b ≥ min b a := by exact le_min h21 h22
  apply le_antisymm h1 h2
  }

lemma exercise_min_assoc : min a (min b c) = min (min a b) c := by {
  apply le_antisymm
  apply le_min
  apply le_min
  apply min_le_left
  calc
    min a (min b c) ≤ min b c := by exact min_le_right a (min b c)
                  _ ≤ b       := by exact min_le_left b c
  calc
    min a (min b c) ≤ min b c := by exact min_le_right a (min b c)
                  _ ≤ c       := by exact min_le_right b c
  apply le_min
  calc
    min (min a b) c ≤ min a b := by exact min_le_left (min a b) c
                  _ ≤ a       := by exact min_le_left a b
  apply le_min
  calc
    min (min a b) c ≤ min a b := by exact min_le_left (min a b) c
                  _ ≤ b       := by exact min_le_right a b
  exact min_le_right (min a b) c
  }

end Min

/- Prove that the following function is continuous.
You can use Continuous.div as the first step,
and use the search techniques to find other relevant lemmas.
ne_of_lt/ne_of_gt will be useful to prove the inequality. -/
lemma exercise_continuity : Continuous (fun x ↦ (sin (x ^ 5) * cos x) / (x ^ 2 + 1)) := by {
  apply Continuous.div
  apply Continuous.mul
  refine Continuous.comp' ?hf.hf.hg ?hf.hf.hf
  · exact continuous_sin
  · exact continuous_pow 5
  · exact continuous_cos
  apply Continuous.add
  apply Continuous.pow
  exact continuous_id
  exact continuous_const
  have h1 (x:ℝ ): x^2+1>0 := by{
    apply add_pos_of_nonneg_of_pos
    · apply pow_two_nonneg
    · linarith
  }
  have h2 (x:ℝ): x^2+1≠ 0 := by{
    apply ne_of_gt
    apply h1
  }
  exact h2
}

/- Prove this only using intro/constructor/obtain/exact -/
lemma exercise_and_comm : ∀ (p q : Prop), p ∧ q ↔ q ∧ p := by {
  intro (p : Prop) (q : Prop)
  constructor
  exact And.symm
  exact And.symm
  }


/-- Prove the following properties of nondecreasing functions. -/
def Nondecreasing (f : ℝ → ℝ) : Prop := ∀ x₁ x₂ : ℝ, x₁ ≤ x₂ → f x₁ ≤ f x₂

lemma exercise_nondecreasing_comp (f g : ℝ → ℝ) (hg : Nondecreasing g) (hf : Nondecreasing f) :
    Nondecreasing (g ∘ f) := by {
  unfold Nondecreasing
  unfold Nondecreasing at hg hf
  intro (x1 : ℝ) (x2 : ℝ) (hx : x1 ≤ x2)
  obtain hfx := hf x1 x2 (by assumption)
  exact hg (f x1) (f x2) (by assumption)
  }


/-- Note: f + g is the function defined by (f + g)(x) := f(x) + g(x).
  simp can simplify (f + g) x to f x + g x. -/
lemma exercise_nondecreasing_add (f g : ℝ → ℝ) (hf : Nondecreasing f) (hg : Nondecreasing g) :
    Nondecreasing (f + g) := by {
  unfold Nondecreasing
  unfold Nondecreasing at hf hg
  intro (x1 : ℝ) (x2 : ℝ) (hx : x1 ≤ x2)
  obtain hfx := hf x1 x2 (by assumption)
  obtain hgx := hg x1 x2 (by assumption)
  simp
  linarith
  }

/-- Prove the following property of even. -/
def EvenFunction (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)

lemma exercise_even_iff (f g : ℝ → ℝ) (hf : EvenFunction f) :
    EvenFunction (f + g) ↔ EvenFunction g := by {
  unfold EvenFunction
  unfold EvenFunction at hf
  simp
  constructor

  intro h1
  intro (x : ℝ)
  calc
    g x = f x + g x - f x          := by ring
      _ = f (-x) + g (-x) - f x    := by rw[h1 x]
      _ = f (-x) + g (-x) - f (-x) := by rw[hf x]
      _ = g (-x)                   := by ring

  intro h2
  intro (x : ℝ)
  rw[h2,hf]
  }
