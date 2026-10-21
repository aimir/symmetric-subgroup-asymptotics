import SymmetricSubgroupAsymptotics.BinaryBooleanFourKernelLeadingClosure
import SymmetricSubgroupAsymptotics.LeadingOperatorColumns

/-! Boolean prefix functions are exactly polynomials in the lower
variables. The finite identities concern individual monomials and bits;
no family of actions or invariant subspaces is enumerated. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates
open BinaryElementaryPairMonomialWidth
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

def bitValue (i : Fin 4) (x : Fin 16) : ZMod 2 := if i ∈ support x then 1 else 0

def DependsOnPrefix (f : V) (r : ℕ) : Prop := ∀ x y : Fin 16,
  (∀ i : Fin 4, i.val < r → bitValue i x = bitValue i y) → f x = f y

set_option maxHeartbeats 2000000 in
private theorem monomial_depends_on_prefix : ∀ (r : Fin 5) (a : Fin 16),
    a.val < 2 ^ r.val → DependsOnPrefix (monomial (support a)) r.val := by
  unfold DependsOnPrefix
  decide

private theorem flip_preserves_lower_bits : ∀ (i j : Fin 4) (x : Fin 16),
    j < i → bitValue j (flipIndex i x) = bitValue j x := by decide

private theorem high_mask_has_variable : ∀ (r : Fin 5) (a : Fin 16),
    2 ^ r.val ≤ a.val → ∃ i : Fin 4, r.val ≤ i.val ∧ i ∈ support a := by decide

private theorem derivative_column_selected : ∀ (i : Fin 4) (a j : Fin 16),
    i ∈ support a →
    (if i ∈ support j then (Pi.single (removeIndex i j) 1 : V) else 0) (removeIndex i a) =
      if j = a then 1 else 0 := by decide

theorem derivative_selected_coefficient (i : Fin 4) (a : Fin 16) (v : V)
    (hi : i ∈ support a) : derivative i v (removeIndex i a) = v a := by
  rw [LeadingOperatorColumns.apply_eq_sum_columns]
  simp only [derivative_basis]
  simp_rw [derivative_column_selected i a _ hi]
  calc
    (∑ j : Fin 16, v j * (if j = a then (1 : ZMod 2) else 0)) =
        v a * (if a = a then 1 else 0) := by
      apply Finset.sum_eq_single a
      · intro j _ hja
        simp only [if_neg hja, mul_zero]
      · intro ha
        exact False.elim (ha (Finset.mem_univ a))
    _ = v a := by simp

private theorem evaluate_sub_sum (v : V) (x y : Fin 16) :
    evaluate v x - evaluate v y =
      ∑ a : Fin 16, v a * (monomial (support a) x - monomial (support a) y) := by
  rw [LeadingOperatorColumns.apply_eq_sum_columns, LeadingOperatorColumns.apply_eq_sum_columns]
  simp_rw [evaluate_basis, mul_sub]
  rw [Finset.sum_sub_distrib]

theorem prefix_polynomial_coefficients_zero (f : V) (r : Fin 5)
    (hf : DependsOnPrefix f r.val) :
    ∀ a : Fin 16, 2 ^ r.val ≤ a.val → evaluate f a = 0 := by
  intro a ha
  obtain ⟨i, hi, hia⟩ := high_mask_has_variable r a ha
  have ht : translate i f = f := by
    funext x
    apply hf
    intro j hj
    exact flip_preserves_lower_bits i j x (by omega)
  have hz : derivative i (evaluate f) = 0 := by
    change evaluate (translate i (evaluate (evaluate f)) - evaluate (evaluate f)) = 0
    rw [evaluate_involutive, ht, sub_self, map_zero]
  have he := congrFun hz (removeIndex i a)
  rw [derivative_selected_coefficient i a _ hia] at he
  exact he

theorem prefix_evaluate_of_coefficients_zero (v : V) (r : Fin 5)
    (hv : ∀ a : Fin 16, 2 ^ r.val ≤ a.val → v a = 0) :
    DependsOnPrefix (evaluate v) r.val := by
  intro x y hxy
  apply sub_eq_zero.mp
  rw [evaluate_sub_sum]
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : a.val < 2 ^ r.val
  · rw [monomial_depends_on_prefix r a ha x y hxy, sub_self, mul_zero]
  · rw [hv a (le_of_not_gt ha), zero_mul]

theorem prefix_add {f g : V} {r : ℕ} (hf : DependsOnPrefix f r) (hg : DependsOnPrefix g r) :
    DependsOnPrefix (f + g) r := by
  intro x y hxy
  exact congrArg₂ (· + ·) (hf x y hxy) (hg x y hxy)

theorem prefix_sub {f g : V} {r : ℕ} (hf : DependsOnPrefix f r) (hg : DependsOnPrefix g r) :
    DependsOnPrefix (f - g) r := by
  intro x y hxy
  exact congrArg₂ (· - ·) (hf x y hxy) (hg x y hxy)

theorem prefix_mul {f g : V} {r : ℕ} (hf : DependsOnPrefix f r) (hg : DependsOnPrefix g r) :
    DependsOnPrefix (f * g) r := by
  intro x y hxy
  exact congrArg₂ (· * ·) (hf x y hxy) (hg x y hxy)

end SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates
