-- All proofs will be shown here
import NewLean
import Mathlib.Tactic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Perm.Basic


/- introduction module theorems -/

-- Additivity of Congruence (mod arithmetic)
-- Multiplicativity of Congruence
-- Power Property of Congruence
-- Fermat's Little Theorem
-- Euler's Theorem


/- Group module theorems -/
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


theorem normal_subgroup_equiv1 (N : Subgroup G) :
  N.Normal ↔ ∀ n ∈ N, ∀ g : G, g * n * g⁻¹ ∈ N := by
  constructor
  -- Case 1: (→) Assume N is normal, prove the conjugation property
  · intro h_normal n hn g
    exact h_normal.conj_mem n hn g

  -- Case 2: (←) Assume the property holds, prove N is normal
  · intro h_prop
    exact { conj_mem := h_prop }



-- parity_of_transpositions
-- orbit_stabilizer_theorem
-- first_isomorphism_theorem
-- second_isomorphism_theorem
-- third_isomorphism_theorem



/- Ring theory and Field thoery module theorems -/
