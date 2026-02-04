import NewLean
import Mathlib.Tactic
import Mathlib.Data.Int.ModEq
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib


----------------------------------
-- introduction module theorems --

-- Additivity of Congruence (mod arithmetic)
theorem add_congruence (a b c d n : ℤ)
  (h1 : n ∣ (a - b))
  (h2 : n ∣ (c - d)) :
  n ∣ ((a + c) - (b + d)) := by
  have h_rewrite : (a + c) - (b + d) = (a - b) + (c - d) := by
    ring
  rw [h_rewrite]

  apply dvd_add
  · exact h1
  · exact h2

-- Multiplicativity of Congruence
theorem mul_congruence (a b c d n : ℤ)
  (h1 : n ∣ (a - b))
  (h2 : n ∣ (c - d)) :
  n ∣ (a * c - b * d) := by
  have h_id : a * c - b * d = c * (a - b) + b * (c - d) := by ring
  rw [h_id]
  apply dvd_add
  · apply dvd_mul_of_dvd_right h1 -- n divides (a-b), so it divides c(a-b)
  · apply dvd_mul_of_dvd_right h2 -- n divides (c-d), so it divides b(c-d)

-- Power Property of Congruence
theorem pow_congruence (a b n : ℤ) (k : ℕ)
  (h : Int.ModEq n a b) :
  Int.ModEq n (a^k) (b^k) := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
  | succ m ih =>
    rw [pow_succ, pow_succ]
    -- If 'pow_succ' gives you (a^m * a), use 'ih' then 'h'
    exact Int.ModEq.mul ih h


-- Fermat's Little Theorem (by_cases)
-- Euler's Theorem
-- Wilson's Theorem





---------------------------
-- Group module theorems --

variable {G : Type*} [Group G]

theorem identity_is_unique (e' : G)
  (h : ∀ a : G, e' * a = a ∧ a * e' = a) :
  e' = 1 := by
  have h1 : 1 * e' = e' := one_mul e'
  have h2 : 1 * e' = 1 := (h 1).right
  rw [← h1, h2]


theorem inverse_is_unique (a b c : G)
  (h1: a * b = 1) (h2: c * a = 1) :
  b = c := by
    calc
      b = 1 * b   := by rw [one_mul]
      _ = (c * a) * b   := by rw [h2]
      _ = c * (a * b)   := by rw [mul_assoc]
      _ = c * 1   := by rw[h1]
      _ = c   := by rw [mul_one]


theorem left_cancel (a b c : G) (h : a * b = a * c) (h_inv: a⁻¹ * a = 1) : b = c := by
  calc
    b = 1 * b           := by rw [one_mul]
    _ = (a⁻¹ * a) * b   := by rw [h_inv]
    _ = a⁻¹ * (a * b)   := by rw [mul_assoc]
    _ = a⁻¹ * (a * c)   := by rw [h]
    _ = (a⁻¹ * a) * c   := by rw [← mul_assoc]
    _ = 1 * c           := by rw [h_inv]
    _ = c               := by rw [one_mul]


theorem lagrange_theorem [Finite G] (H : Subgroup G) :
  Nat.card G = Nat.card H * H.index := by
  exact (Subgroup.card_mul_index H).symm


theorem normal_subgroup_equiv (N : Subgroup G) :
  N.Normal ↔ ∀ n ∈ N, ∀ g : G, g * n * g⁻¹ ∈ N := by
  constructor
  -- Case 1: (→) Assume N is normal, prove the conjugation property
  · intro h_normal n hn g
    exact h_normal.conj_mem n hn g

  -- Case 2: (←) Assume the property holds, prove N is normal
  · intro h_prop
    exact { conj_mem := h_prop }



-- parity_of_transpositions
variable {α : Type} [Fintype α] [DecidableEq α] -- Let n be a finite set (like Fin n)

theorem parity_of_transpositions (factors : List (Equiv.Perm α))
    (h_are_transpositions : ∀ τ ∈ factors, ∃ i j, i ≠ j ∧ τ = Equiv.swap i j) :
    (Equiv.Perm.sign factors.prod : ℤ) = (-1)^(factors.length) := by
  induction factors with -- Induction on the list of factors
  | nil =>
      simp -- base case: empty product is identity, sign is 1, length 0.
  | cons τ ts ih =>
      -- head
      have h_head : ∃ i j, i ≠ j ∧ τ = Equiv.swap i j :=
        h_are_transpositions τ (by simp)

      -- tail
      have h_tail : ∀ t ∈ ts, ∃ i j, i ≠ j ∧ t = Equiv.swap i j :=
        fun t ht => h_are_transpositions t (by simp [ht])

      obtain ⟨i, j, hij, rfl⟩ := h_head

      -- Calculate: sign(τ * ts.prod) = sign(τ) * sign(ts.prod)
      -- We use the homomorphism property
      rw [List.prod_cons, MonoidHom.map_mul]

      -- sign of a swap
      simp [Equiv.Perm.sign_swap hij]

      -- apply IH
      rw [ih h_tail]

      -- arithmetic
      simp [pow_succ]



-- orbit_stabilizer_theorem
-- first_isomorphism_theorem
-- second_isomorphism_theorem
-- third_isomorphism_theorem





--------------------------------------------------
-- Ring theory and Field thoery module theorems --




-- The Correspondence Theorem
  -- Defining the basic structure of a Ring manually for the proof context
structure SimpleRing (R : Type) where
  add : R → R → R
  mul : R → R → R
  zero : R
  neg : R → R
  -- Axioms simplified for the sake of the correspondence proof
  add_comm : ∀ a b : R, add a b = add b a
  mul_assoc : ∀ a b c : R, mul (mul a b) c = mul a (mul b c)
  distrib : ∀ a b c : R, mul a (add b c) = add (mul a b) (mul a c)

  -- An Ideal is a subset that is an additive subgroup and "Sticky"
structure IsIdeal {R : Type} (ring : SimpleRing R) (I : Set R) : Prop where
  has_zero : ring.zero ∈ I
  add_mem : ∀ {a b}, a ∈ I → b ∈ I → ring.add a b ∈ I
  sticky_left : ∀ {a r}, a ∈ I → ring.mul r a ∈ I
  sticky_right : ∀ {a r}, a ∈ I → ring.mul a r ∈ I

  variable {R S : Type} {ringR : SimpleRing R} {ringS : SimpleRing S}

theorem ideal_preimage (f : R → S)
  (f_add : ∀ a b, f (ringR.add a b) = ringS.add (f a) (f b))
  (f_mul : ∀ a b, f (ringR.mul a b) = ringS.mul (f a) (f b))
  (f_zero : f ringR.zero = ringS.zero)
  (J' : Set S) (hJ' : IsIdeal ringS J') :
  IsIdeal ringR { x | f x ∈ J' } := by
  constructor
  · -- Contains Zero
    simp
    rw [f_zero]
    exact hJ'.has_zero
  · -- Closed under Addition
    intro a b ha hb
    simp at *
    rw [f_add]
    exact hJ'.add_mem ha hb
  · -- Sticky Left
    intro a r ha
    simp at *
    rw [f_mul]
    exact hJ'.sticky_left ha
  · -- Sticky Right
    intro a r ha
    simp at *
    rw [f_mul]
    exact hJ'.sticky_right ha

  -- Correspondence
theorem preimage_contains_kernel (f : R → S) (I : Set R)
  (h_ker : ∀ x, x ∈ I ↔ f x = ringS.zero)
  (J' : Set S) (hJ' : IsIdeal ringS J') :
  I ⊆ { x | f x ∈ J' } := by
  intro x hx
  simp
  rw [(h_ker x).mp hx]
  exact hJ'.has_zero



-- Finite Integral Domains Theorem
variable {D : Type} [CommRing D] [IsDomain D] [Fintype D]

theorem finite_domain_is_field1 (a : D) (ha : a ≠ 0) : ∃ b : D, a * b = 1 := by
  let f := fun x : D => a * x

  have f_inj : Function.Injective f := by
    intro x y h
    dsimp [f] at h
    exact mul_left_cancel₀ ha h

  have f_surj : Function.Surjective f :=
    (Finite.injective_iff_surjective :
      Function.Injective f ↔ Function.Surjective f).mp f_inj
  obtain ⟨b, hb⟩ := f_surj 1
  exact ⟨b, hb⟩




-- The Field of Fractions Theorem
variable {D : Type} [CommRing D] [IsDomain D]

-- the underlying set of pairs (numerator, denominator)
-- We represent a/b as the structure 'Frac' where b ≠ 0
structure Frac (D : Type) [CommRing D] where
  num : D
  den : D
  den_ne_zero : den ≠ 0

-- Then define the Equivalence Relation
-- a/b ≈ c/d if and only if ad = bc
def equiv (f1 f2 : Frac D) : Prop :=
  f1.num * f2.den = f2.num * f1.den

theorem equiv_trans {f1 f2 f3 : Frac D} (h1 : equiv f1 f2) (h2 : equiv f2 f3) : equiv f1 f3 := by
  unfold equiv at *
  -- Goal: f1.num * f3.den = f3.num * f1.den
  have h : (f1.num * f3.den) * f2.den = (f1.num * f2.den) * f3.den := by ring
  rw [h1] at h -- Now h is (f1.num * f3.den) * f2.den = (f2.num * f1.den) * f3.den
  have h_ready : (f1.num * f3.den) * f2.den = (f2.num * f3.den) * f1.den := by
    rw [h]
    ring
  rw [h2] at h_ready -- h_ready is (f1.num * f3.den) * f2.den = (f3.num * f2.den) * f1.den
  have final_comparison : (f1.num * f3.den) * f2.den = (f3.num * f1.den) * f2.den := by
    rw [h_ready]
    ring

  -- Cancel the f2.den (which is non-zero because it's a denominator)
  exact mul_right_cancel₀ f2.den_ne_zero final_comparison



-- The Prime Characteristic Theorem
variable {D : Type} [Ring D] [IsDomain D] -- Let D be an Integral Domain

theorem char_is_prime_or_zero (n : ℕ) [CharP D n] :
    n = 0 ∨ Nat.Prime n := by
  by_cases h : n = 0 -- Suppose n is not 0
  · left; exact h
  · right -- If n is not zero, we show it must be prime.
    haveI : NeZero n := ⟨h⟩
    exact (CharP.char_is_prime_of_pos (R := D) (p := n)).out



-- The Cancellation Law
variable {D : Type} [CommRing D] [IsDomain D]

theorem cancel_left {a b c : D} (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  have h' : a * (b - c) = 0 := by
    calc
      a * (b - c) = a * b - a * c := by ring
      _ = 0 := by rw [h, sub_self]
  -- no zero divisors
  have h'' : b - c = 0 :=
    (mul_eq_zero.mp h').resolve_left ha
  exact sub_eq_zero.mp h''






-- The Polynomial Remainder Theorem
open Polynomial

theorem polynomial_remainder_theorem
  {R : Type} [CommRing R] (p : Polynomial R) (a : R) :
  ∃ q : Polynomial R, p = q * (X - C a) + C (p.eval a) := by
  obtain ⟨q, r, h_eq, h_deg⟩ :=
    Polynomial.exists_quotient_remainder p (X - C a)
  have hmonic : Monic (X - C a) := monic_X_sub_C a
  have hdeg' : r.degree ≤ 0 := by
    have := h_deg hmonic
    simpa using this
  obtain ⟨r₀, hr⟩ := eq_C_of_degree_le_zero hdeg'
  subst hr
  have h_eval := congrArg (eval a) h_eq
  simp at h_eval

  refine ⟨q, ?_⟩
  simpa [h_eval] using h_eq




-- The Factor Theorem
variable {F : Type} [Field F]

theorem factor_theorem (f : F[x]) (a : F) :
    (X - C a) ∣ f ↔ f.eval a = 0 := by
  constructor
  · intro h
    obtain ⟨q, hq⟩ := h
    rw [hq]
    simp [eval_mul, eval_sub, eval_X, eval_C]

  · intro h_root
    have h_rem := mod_X_sub_C f a

    rw [h_root] at h_rem
    rw [← dvd_iff_modByMonic_eq_zero (monic_X_sub_C a)]
    exact h_rem



-- Gauss's Lemma
theorem gauss_lemma
  {R : Type} [CommRing R] [IsDomain R]
  (p q : Polynomial R)
  (hp : p.IsPrimitive)
  (hq : q.IsPrimitive) :
  (p * q).IsPrimitive :=
by
  exact hp.mul hq



-- Maximality-Field Theorem
-- Primality-Domain Theorem
-- Chinese Remainder Theorem
