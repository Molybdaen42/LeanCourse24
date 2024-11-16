/-

 Assignment 05
 -----------------------------------
 Nora Depenheuer & Joachim Roscher

-/

--import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
noncomputable section
open Real Function Nat BigOperators Set Finset
open Classical


/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapters 5 (mostly section 2) and 6 (mostly sections 1 and 2).

* Do the exercises corresponding to these sections in the LeanCourse/MIL folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises under "Exercises to hand-in". Deadline: 5.11.

* Make sure the file you hand-in compiles without error.
  Use sorry if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/

/- A note on definitions -/

lemma my_lemma : 3 + 1 = 4 := rfl
def myThree : ℕ := 3

/-
Tactics like simp and rw will not unfold definitions unless instructed to.
Tactics like exact and apply will unfold definitions if needed.
Uncomment the following lines one-by-one to see the difference. -/

example : myThree + 1 = 4 := by
  -- rw [my_lemma] -- fails
  -- simp [my_lemma] -- fails to use my_lemma
  -- exact my_lemma -- works
  -- apply my_lemma -- works
  -- rw [myThree, my_lemma] -- works after instructing rw to unfold the definition
  -- simp [myThree] -- works after instructing simp to unfold the definition
                    -- (it doesn't need my_lemma to then prove the goal)
  sorry


/- The following exercises are to practice with casts. -/
example (n : ℤ) (h : (n : ℚ) = 3) : 3 = n := by {
  norm_cast at h
  symm; assumption
  }

example (n m : ℕ) (h : (n : ℚ) + 3 ≤ 2 * m) : (n : ℝ) + 1 < 2 * m := by {
  norm_cast at h
  norm_cast
  linarith
  }

example (n m : ℕ) (h : (n : ℚ) = m ^ 2 - 2 * m) : (n : ℝ) + 1 = (m - 1) ^ 2 := by {
  sorry
  }

example (n m : ℕ) : (n : ℝ) < (m : ℝ) ↔ n < m := by {
  sorry
  }

example (n m : ℕ) (hn : 2 ∣ n) (h : n / 2 = m) : (n : ℚ) / 2 = m := by {
  sorry
  }

example (q q' : ℚ) (h : q ≤ q') : exp q ≤ exp q' := by {
  sorry
  }

example (n : ℤ) (h : 0 < n) : 0 < Real.sqrt n := by {
  sorry
  }

/- Working with Finset is very similar to working with Set.
However, some notation, such as f '' s or 𝒫 s doesn't exist for Finset. -/
example (s t : Finset ℕ) : (s ∪ t) ∩ t = (s ∩ t) ∪ t := by {
  ext x
  constructor
  · intro h
    obtain x_in_t : x ∈ t := by exact Finset.mem_of_mem_inter_right h
    exact Finset.mem_union_right (s ∩ t) x_in_t
  · intro h
    obtain x_in_s_cap_t| x_in_t := Finset.mem_union.mp h
    · obtain x_in_t : x ∈ t := by exact Finset.mem_of_mem_inter_right x_in_s_cap_t
      obtain x_in_s_cup_t : x ∈ s ∪ t := by exact Finset.mem_union_right s x_in_t
      exact mem_inter_of_mem x_in_s_cup_t x_in_t
    · obtain x_in_s_cup_t : x ∈ s ∪ t := by exact Finset.mem_union_right s x_in_t
      exact mem_inter_of_mem x_in_s_cup_t x_in_t
  }

example {α β : Type*} (f : α → β) (s : Finset α) (y : β) : y ∈ s.image f ↔ ∃ x ∈ s, f x = y := by {
  sorry
  }

/- Disjoint can be used to state that two (fin)sets are disjoint.
Use Finset.disjoint_left (or Set.disjoint_left) to unfold its definition.
If you have x ∈ t \ s apply simp first to get a conjunction of two conditions.
-/
example {α : Type*} (s t : Finset α) : Disjoint s (t \ s) := by {
  sorry
  }


/- Let's define the Fibonacci sequence -/
def fibonacci : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) => fibonacci (n + 1) + fibonacci n

/- Prove the following exercises by induction. -/

example (n : ℕ) : ∑ i in range n, fibonacci (2 * i + 1) = fibonacci (2 * n) := by {
  sorry
  }

example (n : ℕ) : ∑ i in range n, (fibonacci i : ℤ) = fibonacci (n + 1) - 1 := by {
  sorry
  }

example (n : ℕ) : 6 * ∑ i in range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) := by {
  sorry
  }

def fac : ℕ → ℕ
  | 0       => 1
  | (n + 1) => (n + 1) * fac n

theorem pow_two_le_fac (n : ℕ) : 2 ^ n ≤ fac (n + 1) := by {
  sorry
  }

example (n : ℕ) : fac n = ∏ i in range n, (i + 1) := by {
  sorry
  }

example (n : ℕ) : fac (2 * n) = fac n * 2 ^ n * ∏ i in range n, (2 * i + 1) := by {
  sorry
  }





/- Exercise.
Define scalar multiplication of a real number and a Point. -/

@[ext] structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

-- give definition here
def scalar_mult (a : ℝ) (b : Point) : Point where
  x := a * b.x
  y := a * b.y
  z := a * b.z


/- Exercise.Define Pythagorean triples, i.e. triples a b c : ℕ with a^2 + b^2 = c^2.
Give an example of a Pythagorean triple, and show that multiplying a Pythagorean triple by a
constant gives another Pythagorean triple. -/

-- give definition here
structure PythTriple where
  a : ℕ
  b : ℕ
  c : ℕ
  h : a^2 + b^2 = c^2



/- Prove that triples of equivalent types are equivalent. -/

@[ext] structure Triple (α : Type*) where
  x : α
  y : α
  z : α

example (α β : Type*) (e : α ≃ β) : Triple α ≃ Triple β := by {
  obtain ⟨f, g, hleft, hright⟩ := e
  refine (Equiv.ofBijective ?f ?hf)
  · let F : Triple α → Triple β := fun A ↦ ⟨f A.x, f A.y, f A.z⟩
    use F
  · let G : Triple β → Triple α := fun B ↦ ⟨g B.x, g B.y, g B.z⟩
    simp
    refine bijective_iff_has_inverse.mpr ?hf.a
    constructor
    · simp [LeftInverse, Function.RightInverse]
      constructor
      · intro A
        sorry
      · sorry
    · use G
}



/- 5. Show that if G is an abelian group then triples from elements of G is an abelian group. -/

class AbelianGroup' (G : Type*) where
  add (x : G) (y : G) : G
  comm (x y : G) : add x y = add y x
  assoc (x y z : G) : add (add x y) z = add x (add y z)
  zero : G
  add_zero : ∀ x : G, add x zero = x
  neg : G → G
  add_neg : ∀ x : G, add x (neg x) = zero

example (G : Type*) [AbelianGroup' G] : AbelianGroup' (Triple G) := sorry



/-! # Exercises to hand-in. -/

/- Exercise.
Define the structure of "strict bipointed types", i.e. a type together with 2 unequal points
x₀ ≠ x₁ in it.
Then state and prove the lemma that for any element of a strict bipointed type we have
∀ z, z ≠ x₀ ∨ z ≠ x₁. -/

-- give the definition here

-- state and prove the lemma here


/- Prove by induction that ∑_{i = 0}^{n} i^3 = (∑_{i=0}^{n} i) ^ 2. -/
open Finset in

-- copy the lemme from the lecture
lemma little_gauss (n : ℕ) : ∑ i in range (n + 1), (i : ℚ) = n * (n + 1) / 2 := by {
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    field_simp
    ring
  }

lemma sum_cube_eq_sq_sum (n : ℕ) :
    (∑ i in range (n + 1), (i : ℚ) ^ 3) = (∑ i in range (n + 1), (i : ℚ)) ^ 2 := by {
  induction n with
  | zero =>
  simp
  | succ n ih =>
  -- it's easier to understand the equations when beginning with the right hand side
  symm
  calc
    (∑ i ∈ Finset.range (n + 1 + 1), (i : ℚ)) ^ 2
      -- take the case i = n+1 out of the sum
      = (∑ i ∈ Finset.range (n + 1), (i : ℚ) + (n+1)) ^ 2 := by simp [Finset.sum_range_succ]
      -- 1st binomial formula
    _ = (∑ i ∈ Finset.range (n + 1), (i : ℚ)) ^ 2 + 2*(∑ i ∈ Finset.range (n + 1), (i : ℚ))*(n+1) + (n+1)^2 := by exact add_pow_two (∑ i ∈ Finset.range (n + 1), (i : ℚ)) (↑n + 1)
      -- little gauss from the lecture
    _ = (∑ i ∈ Finset.range (n + 1), (i : ℚ)) ^ 2 + 2*(n*(n+1)/2)*(n+1) + (n+1)^2 := by simp [little_gauss]
      -- some boring calculations
    _ = (∑ i ∈ Finset.range (n + 1), (i : ℚ)) ^ 2 + (n+1)^3 := by ring
      -- induction hypothesis and we're done
    _ = ∑ i ∈ Finset.range (n + 1 + 1), (i : ℚ) ^ 3 := by simp [ih, Finset.sum_range_succ]
  }

/-
Suppose (A i)_i is a sequence of sets indexed by a well-ordered type
(this is an order where every nonempty set has a minimum element).
We now define a new sequence by C n = A n \ (⋃ i < n, A i).
In this exercise, we show that the new sequence is pairwise disjoint but has the same union as the
original sequence.
-/
lemma disjoint_unions {ι α : Type*} [LinearOrder ι] [wf : WellFoundedLT ι] (A C : ι → Set α)
  (hC : ∀ i, C i = A i \ ⋃ j < i, A j) : Pairwise (Disjoint on C) ∧ ⋃ i, C i = ⋃ i, A i := by {
  have h := wf.wf.has_min -- this hypothesis allows you to use well-orderedness
  constructor
  · -- to show: Pairwise (Disjoint on C)
    unfold Disjoint Pairwise
    simp
    intro i j i_neq_j X X_subset_Ci X_subset_Cj

    -- to show: X = ∅. Or equivalently, x ∈ X → False
    ext x; simp; by_contra x_in_X

    -- unfold C
    rw [hC i] at X_subset_Ci
    rw [hC j] at X_subset_Cj
    obtain x_in_Ci := X_subset_Ci x_in_X -- x ∈ C i
    obtain x_in_Cj := X_subset_Cj x_in_X -- x ∈ C j

    -- We have i < j or j < i
    obtain i_lt_j | j_lt_i := lt_or_gt_of_ne i_neq_j
    · -- case i < j. Then follows x ∉ C j
      have h' : x ∈ A i := by exact mem_of_mem_diff x_in_Ci
      have h'' : x ∈ ⋃ j' < j, A j' := by exact Set.mem_biUnion i_lt_j h'
      have h''' : ¬x ∈ A j \ ⋃ j' < j, A j' := by exact not_mem_diff_of_mem h''
      contradiction
    · -- case j < . Then follows x ∉ C i
      have h' : x ∈ A j := by exact mem_of_mem_diff x_in_Cj
      have h'' : x ∈ ⋃ j' < i, A j' := by exact Set.mem_biUnion j_lt_i h'
      have h''' : ¬x ∈ A i \ ⋃ j' < i, A j' := by exact not_mem_diff_of_mem h''
      contradiction

  · -- to show: ⋃ i, C i = ⋃ i, A i
    ext x
    constructor
    · -- ∃ i, x ∈ C i
      simp
      intro i x_in_Ci

      -- to show: ∃ i, x ∈ A i
      use i

      -- use that C i lies in A i
      rw [hC] at x_in_Ci
      exact mem_of_mem_diff x_in_Ci

    · -- ∃ j, x ∈ A j
      simp
      intro j x_in_Aj

      -- to show: ∃ i, x ∈ C i

      -- find the minimal i s.t. x ∈ A i
      let I := {i : ι | x ∈ A i}
      obtain ⟨i,x_in_Ai,i_is_minimal⟩ := h I (nonempty_of_mem x_in_Aj)
      simp [I] at x_in_Ai
      simp [I] at i_is_minimal
      use i

      by_contra x_nin_Ci
      rw [hC] at x_nin_Ci

      -- since x ∈ A i but x ∉ A i \ ⋃ i' < i, A i', x must be in ⋃ i' < i, A i'
      have h' : x ∈ ⋃ i' < i, A i' := by
        simp at x_nin_Ci ⊢
        exact x_nin_Ci x_in_Ai

      -- we can also show that x ∉ ⋃ i' < i, A i' by minimality of i
      have h' : x ∉ ⋃ i' < i, A i' := by
        simp at x_nin_Ci ⊢
        -- let k < i
        intro k k_lt_i
        -- prove by contradiction
        by_contra x_in_Ak
        -- use minimality of i
        specialize i_is_minimal k x_in_Ak
        rw[lt_iff_not_ge] at k_lt_i
        contradiction

      contradiction
  }



/- Next, we'll prove that if 2 ^ n - 1 is prime, then n is prime.
The first exercise is a preparation, and I've given you a skeleton of the proof for the
second exercise. Note how we do some computations in the integers, since the subtraction on ℕ
is less well-behaved.
(The converse is not true, because 89 ∣ 2 ^ 11 - 1) -/

lemma not_prime_iff (n : ℕ) :
    ¬ Nat.Prime n ↔ n = 0 ∨ n = 1 ∨ ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ n = a * b := by {
  constructor
  · intro h
    rw [Nat.prime_def_lt] at h
    simp at h
    -- h : 2 ≤ n → ∃ m < n, m | n ∧ ¬m = 1
    by_cases h2_le_n : 2 ≤ n
    · -- in the case 2 ≤ n there is such m
      obtain ⟨m, hm_lt_n, hm_div_n, hm_neq_1⟩ := h h2_le_n

      -- we want to prove the right most part of the goal
      right; right

      -- we want to write n as m*k with k = n/m
      let k : ℕ := n/m
      have hn_eq_mk : n = m*k := by exact Eq.symm (Nat.mul_div_cancel' hm_div_n)
      use m
      use k

      -- useful stuff for later
      -- we have n ≠ 0
      have hn_neq_0 : n ≠ 0 := by exact not_eq_zero_of_lt h2_le_n
      -- We have m*k ≠ 0
      rw [hn_eq_mk] at hn_neq_0

      -- there are some things left to show
      constructor
      · -- to show: 2 ≤ m
        refine (two_le_iff m).mpr ?h.left.a
        constructor
        · -- to show: m ≠ 0
          exact Nat.ne_zero_of_mul_ne_zero_left hn_neq_0
        · -- to show: m ≠ 1
          assumption

      · constructor
        · -- to show: 2 ≤ k
          refine (two_le_iff k).mpr ?h.right.left.a
          constructor
          · -- to show: k ≠ 0
            exact Nat.ne_zero_of_mul_ne_zero_right hn_neq_0
          · -- to show: k ≠ 1
            -- if k = 1 ...
            by_contra hk_eq_1
            -- then n = m
            simp [hk_eq_1] at hn_eq_mk
            -- but m < n
            simp [hn_eq_mk] at hm_lt_n
        · -- to show: n = m*k
          assumption

    · -- we want to prove the part n = 0 ∨ n = 1
      rw [← or_assoc]
      left
      -- we work in the natural numbers, so it's equivalent to n ≤ 1 (or ¬2 ≤ n, as in h2_le_n)
      refine le_one_iff_eq_zero_or_eq_one.mp ?_
      exact Nat.le_of_not_lt h2_le_n

  · intro h
    obtain c0|c1|cab := h
    · -- n = 0
      rw [c0]
      trivial

    · -- n = 1
      rw [c1]
      trivial

    · -- ∃ a b, ...
      obtain ⟨a, b, hab1, hab2, hab3⟩ := cab
      rw [hab3]
      have a_neq_1 : a ≠ 1 := by linarith
      have b_neq_1 : b ≠ 1 := by linarith
      exact not_prime_mul a_neq_1 b_neq_1
  }

lemma prime_of_prime_two_pow_sub_one (n : ℕ) (hn : Nat.Prime (2 ^ n - 1)) : Nat.Prime n := by {
  by_contra h2n
  rw [not_prime_iff] at h2n
  obtain rfl|rfl|⟨a, b, ha, hb, rfl⟩ := h2n
  · contradiction
  · contradiction
  have h : (2 : ℤ) ^ a - 1 ∣ (2 : ℤ) ^ (a * b) - 1 := by
    rw [← Int.modEq_zero_iff_dvd]
    calc (2 : ℤ) ^ (a * b) - 1
        ≡ ((2 : ℤ) ^ a) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by rw [pow_mul 2 a b]
      _ ≡ (1 : ℤ) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by {
        -- get rid of the -1
        apply Int.ModEq.sub ?h₁ rfl
        -- get rid of the ^b
        apply Int.ModEq.pow b
        -- now it's trivial
        exact Int.modEq_sub (2 ^ a) 1
      }
      _ ≡ 0 [ZMOD (2 : ℤ) ^ a - 1] := by simp
  have h2 : 2 ^ 2 ≤ 2 ^ a := by exact pow_le_pow_of_le_right Nat.zero_lt_two ha
  have h3 : 1 ≤ 2 ^ a := by linarith
  have h4 : 2 ^ a - 1 ≠ 1 := by zify; simp [h3]; linarith
  have h5 : 2 ^ a - 1 < 2 ^ (a * b) - 1 := by
    apply tsub_lt_tsub_right_of_le h3
    have a_lt_ab : a < a*b := by
      calc
        a < a*2 := by linarith
        _ ≤ a*b := by exact Nat.mul_le_mul_left a hb
    exact (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mpr a_lt_ab
  have h6' : 2 ^ 0 ≤ 2 ^ (a * b) := by exact pow_le_pow_of_le_right Nat.zero_lt_two (Nat.zero_le (a * b))
  have h6 : 1 ≤ 2 ^ (a * b) := h6'
  have h' : 2 ^ a - 1 ∣ 2 ^ (a * b) - 1 := by norm_cast at h
  rw [Nat.prime_def_lt] at hn
  -- split hn
  obtain ⟨hn1,hn2⟩ := hn
  -- use h5 onto hn2
  specialize hn2 (2^a-1) h5
  -- the necessary condition in hn2 is false by h4
  simp [h4] at hn2
  -- but now hn2 and h' are contradictory
  contradiction
  }

#check dvd_iff_mod_eq_zero.mpr
#check odd_of_mod_four_eq_one
#check odd_of_mod_four_eq_three

/- Prove that for positive a and b, a^2 + b and b^2 + a cannot both be squares.
Prove it on paper first! -/
lemma not_isSquare_sq_add_or (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ¬ IsSquare (a ^ 2 + b) ∨ ¬ IsSquare (b ^ 2 + a) := by {
  -- suppose not
  by_contra h
  push_neg at h

  -- suppose x^2 = a^2 + b
  obtain ⟨x, hab⟩ := h.1
  -- and y^2 = b^2 + a
  obtain ⟨y, hba⟩ := h.2
  rw [← Nat.pow_two] at hab hba

  -- We'll consider a^2 + b = x^2 mod 4. For this we need some observations

  -- c^2 is 0 or 1 - it depends on the parity
  have h1 : ∀ c : ℕ, c^2 % 4 = 0 ∨ c^2 % 4 = 1 := by
    intro c
    rcases mod_two_eq_zero_or_one c with h_1|h_2
    · -- if c is even
      left
      -- write c % 2 = 0 as 2 ∣ c and the goal c^2 % 4 = 0 as 4 ∣ c^2
      apply dvd_iff_mod_eq_zero.mpr at h_1
      apply dvd_iff_mod_eq_zero.mp
      -- there is some k s.t. c = 2 * k
      obtain ⟨k,hk⟩ := h_1
      use k^2
      calc
        c^2 = (2*k)^2 := by rw[hk]
          _ = 4 * k^2 := by linarith
    · -- if c is odd
      right
      sorry

  -- Similarly, c is either 0 or 1 mod 2
  have h2 : ∀ c:ℕ, c % 2 = 0 ∨ c % 2 = 1 := by exact mod_two_eq_zero_or_one

  rcases h1 a with h11|h12; rcases h2 b with h21|h22
  -- We analyze cases based on the possible values of a^2 and b modulo 4
  · -- Case 1: a^2 ≡ 0 (mod 4), b ≡ 0 (mod 2)
    -- Let's compute some things
    have h' : x^2 % 2 = 0 := by
      rw [← hab]
      have h'1 : a^2 % 2 = 0 := by sorry
      sorry
    -- Since x^2 is a square an we have x^2 % 4 = 0 or 1, we have
    have h'' : x^2 % 4 = 0 := by
      -- want the first part of (h1 x), so disprove its second part
      sorry

    -- 0 (mod 4) for a perfect square implies both a, b are multiples of higher powers of 2
    sorry
  · sorry
  · sorry

  /- Lösung von ChatGPT: (hx = hab, hy = hba)
  -- Case 1: a^2 ≡ 0 (mod 4), b ≡ 0 (mod 2)
  { rw [h1, h2] at hx, -- h1 should be h11, h2 should be h21
    norm_num at hx,
    have hsq := nat.mod_four_eq_zero_or_one x,
    cases hsq;
    -- This leads to contradictions since squares modulo 4 cannot match the sum
    linarith },

  -- Case 2: a^2 ≡ 0 (mod 4), b ≡ 1 (mod 2)
  { rw [h1, h2] at hx,
    norm_num at hx,
    have hsq := nat.mod_four_eq_zero_or_one x,
    cases hsq;
    linarith },

  -- Case 3: a^2 ≡ 1 (mod 4), b ≡ 0 (mod 2)
  { rw [h1, h2] at hx,
    norm_num at hx,
    have hsq := nat.mod_four_eq_zero_or_one x,
    cases hsq;
    linarith },

  -- Case 4: a^2 ≡ 1 (mod 4), b ≡ 1 (mod 2)
  { rw [h1, h2] at hx,
    norm_num at hx,
    have hsq := nat.mod_four_eq_zero_or_one x,
    cases hsq;
    linarith },
  -/
  }


/-- Let's prove that the positive reals form a group under multiplication.
Note: in this exercise rw and simp will not be that helpful, since the definition is hidden
behind notation. But you can use apply to use the lemmas about real numbers. -/

abbrev PosReal : Type := {x : ℝ // 0 < x}

def groupPosReal : Group PosReal where
  -- define the operations and constants
  mul x y := ⟨x * y, mul_pos x.property y.property⟩
  one := ⟨1, by norm_num⟩
  inv x := ⟨x.val⁻¹, by exact inv_pos.mpr x.property⟩

  -- prove the properties
  mul_assoc x y z := Subtype.ext (mul_assoc x.val y.val z.val)
  one_mul x := Subtype.ext (one_mul x.val)
  mul_one x := Subtype.ext (mul_one x.val)
  inv_mul_cancel x := Subtype.ext (inv_mul_cancel₀ (ne_of_gt x.property))

/-
Compute by induction the cardinality of the powerset of a finite set.

Hints:
* Use Finset.induction as the induction principle, using the following pattern:

  induction s using Finset.induction with
  | empty => sorry
  | @insert x s hxs ih => sorry

* You will need various lemmas about the powerset, search them using Loogle.
  The following queries will be useful for the search:
  Finset.powerset, insert _ _
  Finset.card, Finset.image
  Finset.card, insert _ _
* As part of the proof, you will need to prove an injectivity condition
  and a disjointness condition.
  Separate these out as separate lemmas or state them using have to break up the proof.
* Mathlib already has card_powerset as a simp-lemma, so we remove it from the simp-set,
  so that you don't actually simplify with that lemma.
-/
attribute [-simp] card_powerset
#check Finset.induction

lemma fintype_card_powerset (α : Type*) (s : Finset α) :
    Finset.card (powerset s) = 2 ^ Finset.card s := by {
  induction s using Finset.induction with
    | empty => trivial
    | @insert x s hxs ih =>
    --rw [card_insert_of_not_mem hxs]
    have h : x ∈ (insert x s) := by exact mem_insert_self x s
    have h1 : (insert x s).card = s.card + 1 := by exact card_insert_of_not_mem hxs

    let f : (insert x s).powerset → Finset.range (insert x s).card := sorry
    have f_bij : Bijective f := by sorry

    -- have h2 : (insert x s).powerset = s.powerset ∪ {A | A ∈ (insert x s).powerset ∧ x ∈ A} := by sorry

    sorry
  }
