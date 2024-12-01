import LeanCourse.Common
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Pow

noncomputable section
open BigOperators Function Set Real Filter Classical Topology TopologicalSpace


/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 10.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises under "Exercises to hand-in". Deadline: 3.12.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/

/- You can use `filter_upwards` to conveniently conclude `Eventually` statements from `Eventually`
in one or more hypotheses using the same filter. -/
example {ι : Type*} {L : Filter ι} {f g : ι → ℝ} (h1 : ∀ᶠ i in L, f i ≤ g i)
    (h2 : ∀ᶠ i in L, g i ≤ f i) : ∀ᶠ i in L, f i = g i := by
  filter_upwards [h1, h2] with i h1 h2
  exact le_antisymm h1 h2

example {ι : Type*} {L : Filter ι} {a b : ι → ℤ} (h1 : ∀ᶠ i in L, a i ≤ b i + 1)
    (h2 : ∀ᶠ i in L, b i ≤ a i + 1) (h3 : ∀ᶠ i in L, b i ≠ a i) : ∀ᶠ i in L, |a i - b i| = 1 := by {
  sorry
  }

/- The goal of the following exercise is to prove that
the regular open sets in a topological space form a complete boolean algebra.
`U ⊔ V` is given by `interior (closure (U ∪ V))`.
`U ⊓ V` is given by `U ∩ V`. -/


variable {X : Type*} [TopologicalSpace X]

variable (X) in
structure RegularOpens where
  carrier : Set X
  isOpen : IsOpen carrier
  regular' : interior (closure carrier) = carrier

namespace RegularOpens

/- We write some lemmas so that we can easily reason about regular open sets. -/
variable {U V : RegularOpens X}

instance : SetLike (RegularOpens X) X where
  coe := RegularOpens.carrier
  coe_injective' := fun ⟨_, _, _⟩ ⟨_, _, _⟩ _ => by congr

theorem le_def {U V : RegularOpens X} : U ≤ V ↔ (U : Set X) ⊆ (V : Set X) := by simp
@[simp] theorem regular {U : RegularOpens X} : interior (closure (U : Set X)) = U := U.regular'

@[simp] theorem carrier_eq_coe (U : RegularOpens X) : U.1 = ↑U := rfl

@[ext] theorem ext (h : (U : Set X) = V) : U = V :=
  SetLike.coe_injective h


/- First we want a complete lattice structure on the regular open sets.
We can obtain this from a so-called `GaloisCoinsertion` with the closed sets.
This is a pair of maps
* `l : RegularOpens X → Closeds X`
* `r : Closeds X → RegularOpens X`
with the properties that
* for any `U : RegularOpens X` and `C : Closeds X` we have `l U ≤ C ↔ U ≤ r U`
* `r ∘ l = id`
If you know category theory, this is an *adjunction* between orders
(or more precisely, a coreflection).
-/

/- The closure of a regular open set. Of course mathlib knows that the closure of a set is closed.
(the `simps` attribute will automatically generate the simp-lemma for you that
`(U.cl : Set X) = closure (U : Set X)`
-/
@[simps]
def cl (U : RegularOpens X) : Closeds X :=
  ⟨closure U, sorry⟩

/- The interior of a closed set. You will have to prove yourself that it is regular open. -/
@[simps]
def _root_.TopologicalSpace.Closeds.int (C : Closeds X) : RegularOpens X :=
  ⟨interior C, sorry, sorry⟩

/- Now let's show the relation between these two operations. -/
lemma cl_le_iff {U : RegularOpens X} {C : Closeds X} :
    U.cl ≤ C ↔ U ≤ C.int := by sorry

@[simp] lemma cl_int : U.cl.int = U := by sorry

/- This gives us a GaloisCoinsertion. -/

def gi : GaloisCoinsertion cl (fun C : Closeds X ↦ C.int) where
  gc U C := cl_le_iff
  u_l_le U := by simp
  choice C hC := C.int
  choice_eq C hC := rfl

/- It is now a general theorem that we can lift the complete lattice structure from `Closeds X`
to `RegularOpens X`. The lemmas below give the definitions of the lattice operations. -/

instance completeLattice : CompleteLattice (RegularOpens X) :=
  GaloisCoinsertion.liftCompleteLattice gi

@[simp] lemma coe_inf {U V : RegularOpens X} : ↑(U ⊓ V) = (U : Set X) ∩ V := by
  have : U ⊓ V = (U.cl ⊓ V.cl).int := rfl
  simp [this]

@[simp] lemma coe_sup {U V : RegularOpens X} : ↑(U ⊔ V) = interior (closure ((U : Set X) ∪ V)) := by
  have : U ⊔ V = (U.cl ⊔ V.cl).int := rfl
  simp [this]

@[simp] lemma coe_top : ((⊤ : RegularOpens X) : Set X) = univ := by
  have : (⊤ : RegularOpens X) = (⊤ : Closeds X).int := rfl
  simp [this]

@[simp] lemma coe_bot : ((⊥ : RegularOpens X) : Set X) = ∅ := by
  have : (⊥ : RegularOpens X) = (⊥ : Closeds X).int := rfl
  simp [this]

@[simp] lemma coe_sInf {U : Set (RegularOpens X)} :
    ((sInf U : RegularOpens X) : Set X) =
    interior (⋂₀ ((fun u : RegularOpens X ↦ closure u) '' U)) := by
  have : sInf U = (sInf (cl '' U)).int := rfl
  simp [this]

@[simp] lemma Closeds.coe_sSup {C : Set (Closeds X)} : ((sSup C : Closeds X) : Set X) =
    closure (⋃₀ ((↑) '' C)) := by
  have : sSup C = Closeds.closure (sSup ((↑) '' C)) := rfl
  simp [this]

@[simp] lemma coe_sSup {U : Set (RegularOpens X)} :
    ((sSup U : RegularOpens X) : Set X) =
    interior (closure (⋃₀ ((fun u : RegularOpens X ↦ closure u) '' U))) := by
  have : sSup U = (sSup (cl '' U)).int := rfl
  simp [this]

/- We still have to prove that this gives a distributive lattice.
Warning: these are hard. -/
instance completeDistribLattice : CompleteDistribLattice (RegularOpens X) :=
  CompleteDistribLattice.ofMinimalAxioms
  { completeLattice with
    inf_sSup_le_iSup_inf := by sorry
    iInf_sup_le_sup_sInf := by sorry
    }

/- Finally, we can show that the regular open subsets form a complete Boolean algebra.
Define `compl` and`coe_compl` holds and complete the instance below. -/

structure CompleteBooleanAlgebra.MinimalAxioms (α : Type*) extends
    CompleteDistribLattice.MinimalAxioms α, HasCompl α where
  inf_compl_le_bot : ∀ (x : α), x ⊓ xᶜ ≤ ⊥
  top_le_sup_compl : ∀ (x : α), ⊤ ≤ x ⊔ xᶜ

abbrev CompleteBooleanAlgebra.ofMinimalAxioms {α : Type*}
    (h : CompleteBooleanAlgebra.MinimalAxioms α) : CompleteBooleanAlgebra α where
      __ := h
      le_sup_inf x y z :=
        let z := CompleteDistribLattice.ofMinimalAxioms h.toMinimalAxioms
        le_sup_inf


instance : HasCompl (RegularOpens X) where
  compl U := sorry

@[simp]
lemma coe_compl (U : RegularOpens X) : ↑Uᶜ = interior (U : Set X)ᶜ := sorry

instance completeBooleanAlgebra : CompleteBooleanAlgebra (RegularOpens X) :=
  CompleteBooleanAlgebra.ofMinimalAxioms {
    inf_sSup_le_iSup_inf := completeDistribLattice.inf_sSup_le_iSup_inf
    iInf_sup_le_sup_sInf := completeDistribLattice.iInf_sup_le_sup_sInf
    inf_compl_le_bot := by
      sorry
    top_le_sup_compl := by
      sorry
  }

/-! # Exercises to hand-in. -/

/- Here is a technical property using filters, characterizing when a 2-valued function converges to
a filter of the form `if q then F else G`. The next exercise is a more concrete application.
Useful lemmas here are
* `Filter.Eventually.filter_mono`
* `Filter.Eventually.mono` -/
lemma technical_filter_exercise {ι α : Type*} {p : ι → Prop} {q : Prop} {a b : α}
    {L : Filter ι} {F G : Filter α}
    (hbF : ∀ᶠ x in F, x ≠ b) (haG : ∀ᶠ x in G, x ≠ a) (haF : pure a ≤ F) (hbG : pure b ≤ G) :
    (∀ᶠ i in L, p i ↔ q) ↔
    Tendsto (fun i ↦ if p i then a else b) L (if q then F else G) := by {
  have hab : a ≠ b
  · exact haF hbF
  rw [tendsto_iff_eventually]
  constructor
  · intro h1 P h2
    by_cases hq : q
    · -- case q is true
      simp [hq] at h1 h2

      apply Filter.Eventually.mono h1
      intro i pi
      simp [pi]
      -- Now we just have to show that P a holds
      exact haF h2

    · -- case q is false
      simp [hq] at h1 h2

      apply Filter.Eventually.mono h1
      intro i pi
      simp [pi]
      -- Now we just have to show that P b holds
      exact hbG h2

  · intro h
    by_cases hq : q
    · -- if q holds
      simp [hq] at h ⊢

      let P : α → Prop := fun y ↦ y ≠ b
      have P_eventually: ∀ᶠ (y : α) in F, P y := by
        simp [P]
        exact hbF
      -- this we can use on h
      specialize h P_eventually
      simp [P] at h
      -- and get our result
      exact h.1

    · -- if q does not hold
      simp [hq] at h ⊢

      let P : α → Prop := fun y ↦ y ≠ a
      have P_eventually: ∀ᶠ (y : α) in G, P y := by
        simp [P]
        exact haG
      -- this we can use on h
      specialize h P_eventually
      simp [P] at h
      -- and get our result
      exact h.1

  }
#check Filter.Eventually.filter_mono
#check Filter.Eventually.mono

/- To be more concrete, we can use the previous lemma to prove the following.
if we denote the characteristic function of `A` by `1_A`, and `f : ℝ → ℝ` is a function,
then  `f * 1_{s i}` tends to `f * 1_t` iff `x ∈ s i` is eventually equivalent to
`x ∈ t` for all `x`. (note that this does *not* necessarily mean that `s i = t` eventually).
`f * 1_t` is written `indicator t f` in Lean.
Useful lemmas for this exercise are `indicator_apply`, `apply_ite` and `tendsto_pi_nhds`. -/
lemma tendsto_indicator_iff {ι : Type*} {L : Filter ι} {s : ι → Set ℝ} {t : Set ℝ} {f : ℝ → ℝ}
    (ha : ∀ x, f x ≠ 0) :
    (∀ x, ∀ᶠ i in L, x ∈ s i ↔ x ∈ t) ↔
    Tendsto (fun i ↦ indicator (s i) f) L (𝓝 (indicator t f)) := by {
  constructor
  · intro h1
    -- getting rid of f - or do we?
    apply tendsto_pi_nhds.mpr

    intro x
    --specialize h1 x
    --specialize ha x

    simp [indicator_apply]
    rw [tendsto_iff_eventually]
    intro p h2

    filter_upwards [h1 x]
    intro i hi

    rw [hi]

    simp [apply_ite] at h2 ⊢
    --apply technical_filter_exercise
    by_cases hx_in_t : x ∈ t
    · -- suppose x ∈ t
      simp [hx_in_t] at h2 ⊢
      simp [eventually_iff] at h2
      exact mem_of_mem_nhds h2
    · simp [hx_in_t] at h2 ⊢
      exact mem_of_mem_nhds h2
  · intro h x
    simp [tendsto_pi_nhds] at h
    specialize h x
    simp [indicator_apply, apply_ite 𝓝] at h

    --(hbF : ∀ᶠ x in F, x ≠ b) (haG : ∀ᶠ x in G, x ≠ a) (haF : pure a ≤ F) (hbG : pure b ≤ G)
    have hbF : ∀ᶠ y in 𝓝 (f x), y ≠ 0 := by
      exact ContinuousAt.eventually_ne (fun ⦃U⦄ a ↦ a) (ha x)
    have haG : ∀ᶠ y in 𝓝 0, y≠ f x := by
      exact ContinuousAt.eventually_ne (fun ⦃U⦄ a ↦ a) fun a ↦ ha x (id (Eq.symm a))
    have haF : pure (f x) ≤ 𝓝 (f x) := by
      exact intervalIntegral.FTCFilter.pure_le
    have hbG : pure (0:ℝ ) ≤ 𝓝 0 := by
      exact intervalIntegral.FTCFilter.pure_le
    simp [ technical_filter_exercise hbF haG haF hbG]
    exact h
  }
#check indicator_apply
#check apply_ite
#check tendsto_pi_nhds
