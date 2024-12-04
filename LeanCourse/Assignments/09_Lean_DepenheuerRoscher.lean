/-
===================================
Assignment 09
===================================
Nora Depenheuer & Joachim Roscher
===================================
-/

import LeanCourse.Common
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.Convolution
import Mathlib.Data.Real.Irrational
import Mathlib.MeasureTheory.Function.Jacobian
open BigOperators Function Set Real Topology Filter
open MeasureTheory Interval Convolution ENNReal
noncomputable section

noncomputable section
open BigOperators Function Set Real Filter Classical Topology TopologicalSpace


/-
* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 11 & 12.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises under "Exercises to hand-in". Deadline: 10.12.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/


example (x : ℝ) :
    deriv (fun x ↦ Real.exp (x ^ 2)) x = 2 * x * Real.exp (x ^ 2) := by {
  sorry
  }

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {n : ℕ∞} in
/- In this exercise you should combine the right lemmas from the library,
in particular `IsBoundedBilinearMap.contDiff`. -/
example (L : E →L[𝕜] E →L[𝕜] E) (f g : E → E) (hf : ContDiff 𝕜 n f)
    (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n (fun z : E × E ↦ L (f z.1) (g z.2)) := by {
  sorry
  }


section

variable (α : Type*)
 [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]

/-
In the next three exercises we will show that every continuous injective function `ℝ → ℝ` is
either strictly monotone or strictly antitone.

We start by proving a slightly harder version of the exercise in class.
We generalize the real numbers to an arbitrary type `α`
that satisfies all the conditions required for the intermediate value theorem.
If you want to prove this by using the intermediate value theorem only once,
then use `intermediate_value_uIcc`.
`uIcc a b` is the unordered interval `[min a b, max a b]`.
Useful lemmas: `uIcc_of_le` and `mem_uIcc`. -/
--lemma mono_exercise_part1 {f : α → α} (hf : Continuous f) (h2f : Injective f) {a b x : α}
--    (hab : a ≤ b) (h2ab : f a < f b) (hx : a ≤ x) : f a ≤ f x := by {
--  sorry
--  }

/- Now use this and the intermediate value theorem again
to prove that `f` is at least monotone on `[a, ∞)`. -/
lemma mono_exercise_part2 {f : α → α} (hf : Continuous f) (h2f : Injective f)
    {a b : α} (hab : a ≤ b) (h2ab : f a < f b) : StrictMonoOn f (Ici a) := by {
  sorry
  }

/-
Now we can finish just by using the previous exercise multiple times.
In this proof we take advantage that we did the previous exercise for an arbitrary order,
because that allows us to apply it to `ℝ` with the reversed order `≥`.
This is called `OrderDual ℝ`. This allows us to get that `f` is also strictly monotone on
`(-∞, b]`.
Now finish the proof yourself.
You do not need to apply the intermediate value theorem in this exercise.
-/
lemma mono_exercise_part3 (f : ℝ → ℝ) (hf : Continuous f) (h2f : Injective f) :
    StrictMono f ∨ StrictAnti f := by {
  have : ∀ {a b : ℝ} (hab : a ≤ b) (h2ab : f a < f b), StrictMonoOn f (Iic b)
  · intro a b hab h2ab
    have := mono_exercise_part2 (OrderDual ℝ) hf h2f hab h2ab
    rw [strictMonoOn_dual_iff.symm] at this
    exact this
  -- sorry
  by_contra h
  simp [not_or, StrictMono, StrictAnti] at h
  obtain ⟨⟨a, b, hab, h2ab⟩, ⟨c, d, hcd, h2cd⟩⟩ := h
  have h3cd : f c < f d := h2cd.lt_of_ne (h2f.ne hcd.ne)
  have h1 : a < c
  · by_contra h
    simp at h
    exact mono_exercise_part2 ℝ hf h2f hcd.le h3cd h (h.trans hab.le) hab |>.not_le h2ab
  have h2 : f c ≤ f a
  · by_contra h
    simp at h
    exact mono_exercise_part2 ℝ hf h2f h1.le h left_mem_Ici hab.le hab |>.not_le h2ab
  exact this hcd.le h3cd (h1.le.trans hcd.le) hcd.le h1 |>.not_le h2
  }

end

/-
Let's prove that the absolute value function is not differentiable at 0.
You can do this by showing that the left derivative and the right derivative do exist,
but are not equal. We can state this with `HasDerivWithinAt`
To make the proof go through, we need to show that the intervals have unique derivatives.
An example of a set that doesn't have unique derivatives is the set `ℝ × {0}`
as a subset of `ℝ × ℝ`, since that set doesn't contains only points in the `x`-axis,
so within that set there is no way to know what the derivative of a function should be
in the direction of the `y`-axis.

The following lemmas will be useful
* `HasDerivWithinAt.congr`
* `uniqueDiffWithinAt_convex`
* `HasDerivWithinAt.derivWithin`
* `DifferentiableAt.derivWithin`.
-/

example : ¬ DifferentiableAt ℝ (fun x : ℝ ↦ |x|) 0 := by {
  intro h
  have h1 : HasDerivWithinAt (fun x : ℝ ↦ |x|) 1 (Ici 0) 0 := by {
    sorry
    }
  have h2 : HasDerivWithinAt (fun x : ℝ ↦ |x|) (-1) (Iic 0) 0 := by {
    sorry
    }
  have h3 : UniqueDiffWithinAt ℝ (Ici (0 : ℝ)) 0 := by {
  sorry
  }
  have h4 : UniqueDiffWithinAt ℝ (Iic (0 : ℝ)) 0 := by {
  sorry
  }
  -- sorry
  have h5 := h.derivWithin h3
  rw [← h.derivWithin h4, h1.derivWithin h3, h2.derivWithin h4] at h5
  norm_num at h5
  }



/- There are special cases of the change of variables theorems for affine transformations
(but you can also use the change of variable theorem from the lecture) -/
example (a b : ℝ) :
    ∫ x in a..b, sin (x / 2 + 3) =
    2 * cos (a / 2 + 3) - 2 * cos (b / 2  + 3) := by {
  sorry
  }

/- Use the change of variables theorem for this exercise. -/
example (f : ℝ → ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    ∫ x in s, exp x * f (exp x) = ∫ y in exp '' s, f y := by {
  sorry
  }

example (x : ℝ) : ∫ t in (0)..x, t * exp t = (x - 1) * exp x + 1 := by {
  sorry
  }

example (a b : ℝ) : ∫ x in a..b, 2 * x * exp (x ^ 2) =
    exp (b ^ 2) - exp (a ^ 2) := by {
  sorry
  }


/-! # Exercises to hand-in. -/

/- This is a copy of `mono_exercise_part1` above. See the comments there for more info. -/
-- Copied from above:
/- We generalize the real numbers to an arbitrary type `α`
that satisfies all the conditions required for the intermediate value theorem.
If you want to prove this by using the intermediate value theorem only once,
then use `intermediate_value_uIcc`.
`uIcc a b` is the unordered interval `[min a b, max a b]`.
Useful lemmas: `uIcc_of_le` and `mem_uIcc`. -/
variable (α : Type*) [ConditionallyCompleteLinearOrder α]
  [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α] in
lemma mono_exercise_part1_copy {f : α → α} (hf : Continuous f) (h2f : Injective f) {a b x : α}
    (hab : a ≤ b) (h2ab : f a < f b) (hx : a ≤ x) : f a ≤ f x := by {
  -- h2f, hab, h2ab gives us that f is strictly monotone. But that's more than we need to show, so we won't prove it.
  have h1 : [[f a, f b]] ⊆ f '' [[a, b]] := intermediate_value_uIcc (Continuous.continuousOn hf)
  rw [uIcc_of_le hab, uIcc_of_le (le_of_lt h2ab)] at h1
  have h2 : [[f a, f x]] ⊆ f '' [[a, x]] := intermediate_value_uIcc (Continuous.continuousOn hf)
  rw [uIcc_of_le hx] at h2
  have ha_lt_b : a < b := by 
    have : f a ≠ f b := ne_of_lt h2ab
    exact lt_of_le_of_ne hab fun a_1 => this (congrArg f a_1)

  by_contra hcontra
  rw [not_le] at hcontra
  -- suppose a ≤ x, a ≤ b s.t. f(x) < f(a) < f(b)
  -- Since f(a) ≠ f(x), we know that a < x
  have ha_lt_x : a < x := by
    have : f a ≠ f x := (ne_of_lt hcontra).symm
    exact lt_of_le_of_ne hx fun a_1 => this (congrArg f a_1)

  -- use the IVT on the interval [[x, b]]
  have hIVT : [[f x, f b]] ⊆ f '' [[x, b]] := intermediate_value_uIcc (Continuous.continuousOn hf)
  have : f a ∈ [[f x, f b]] := by
    simp [mem_uIcc]; left; exact ⟨le_of_lt hcontra, le_of_lt h2ab⟩  
  -- It gives us some x' ∈ [[x, b]] with f(x') = f(a)
  obtain ⟨x',hx', hfx'_eq_fa⟩ := hIVT this
  
  -- This gives us a contradiction by injectivity of f:
  -- on the one hand, a ∈ [[x, b]]...
  have : a = x' := h2f (h2f (congrArg f hfx'_eq_fa.symm))
  rw [← this] at hx'
  -- but on the other hand, a ∉ [[x, b]]
  have hc2 : a ∉ [[x, b]] := by exact not_mem_uIcc_of_lt ha_lt_x ha_lt_b
  contradiction
  }

/- Prove the following using the change of variables theorem. -/
lemma change_of_variables_exercise (f : ℝ → ℝ) :
    ∫ x in (0)..π, sin x * f (cos x) = ∫ y in (-1)..1, f y := by {
  -- want to show: ∫ y in (-1)..1, f y = ∫ x in (0)..π, sin x * f (cos x)
  symm

  -- Want to use the change of variables theorem. 
  -- First, we want to define the necessary sets and functions and prove their properties.
  let s := [[0,π]]
  let g := cos
  let g' := -sin
  have hs : MeasurableSet s := by exact measurableSet_uIcc
  have hg' : ∀ x ∈ s, HasDerivWithinAt g (g' x) s x := by
    intro x hx
    simp [g,g',s]
    apply HasDerivAt.hasDerivWithinAt
    exact hasDerivAt_cos x
  have hg : InjOn g s := by
    simp [g,s, uIcc_of_le pi_nonneg]
    exact injOn_cos
  
  -- Use the change of variables theorem
  convert integral_image_eq_integral_abs_deriv_smul hs hg' hg f 
  
  -- tidying it up
  · have : g '' s = [[-1, 1]] := by sorry
    rw [this]
    sorry
  · simp [s, g, g']
    have : ∀ x ∈ [[0,π]], |sin x| = sin x := by sorry
    --simp [this]
    sorry
  }
/-
(hs : MeasurableSet s) (hg' : ∀ x ∈ s, HasDerivWithinAt g (g' x) s x) (hg : InjOn g s)
  (f : ℝ → F) : ∫ (x : ℝ) in g '' s, f x = ∫ (x : ℝ) in s, |g' x| • f (g x)
-/
#check integral_image_eq_integral_abs_deriv_smul 
