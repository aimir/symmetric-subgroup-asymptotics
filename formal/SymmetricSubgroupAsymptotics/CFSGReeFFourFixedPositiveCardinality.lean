import SymmetricSubgroupAsymptotics.CFSGReeFFourInversionPeeling
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedSubgroupPeeling

/-! Exact q^12 cardinality of the actual original exceptional-fixed
positive subgroup, obtained from eight genuine opposed peels. This
concerns the full fixed group, including m=0, and does not identify the
Tits derived subgroup or its Sylow subgroup with the full fixed group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFixedPositiveCardinality
open CFSGOpposedSubgroupPeeling CFSGOpposedSubgroupPeelingChain
open CFSGReeFFourInversionPeelingWords CFSGReeFFourInversionPeeling
open CFSGReeFFourFixedSubgroupPeeling CFSGReeFFourSimpleInversionBlocks
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourOppositionFixedPositiveNegative
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedAmbientHom

private instance fixed_finite (m : ℕ) : Finite (originalModelFixed m) :=
  Finite.of_injective (fixedAmbientHom m) (fixedAmbientHom_injective m)

def prefixWeight (head : Bool) (n : ℕ) : ℕ :=
  ∑ j∈Finset.range n, if axis head j then 2 else 1

theorem step_inversion_card (m : ℕ) (head : Bool) (j : ℕ) :
    Nat.card (inversionPart (fixedPositive m) (fixedNegative m) (step m head j)) =
      (2^(2*m+1))^(if axis head j then 2 else 1) :=
  simple_inversion_card m (axis head j)

theorem inversion_product_card (m : ℕ) (head : Bool) (n : ℕ) :
    (∏ j∈Finset.range n,
      Nat.card (inversionPart (fixedPositive m) (fixedNegative m) (step m head j))) =
        (2^(2*m+1))^(prefixWeight head n) := by
  simp_rw [step_inversion_card]
  exact Finset.prod_pow_eq_pow_sum (Finset.range n)
    (fun j=>if axis head j then 2 else 1) (2^(2*m+1))

theorem fixedPositive_card_factorization (m : ℕ) (head : Bool) (n : ℕ) (hn : n≤8) :
    Nat.card (fixedPositive m) =
      Nat.card (residual (fixedPositive m) (step m head) n) *
        (2^(2*m+1))^(prefixWeight head n) := by
  have h := card_eq_residual_mul_blocks (fixedPositive m) (fixedNegative m)
    (step m head) n (fixed_positive_negative_disjoint m)
    (fun j hj=>simple_block_le_residual m head ⟨j,Nat.lt_of_lt_of_le hj hn⟩)
    (fun j _=>fixed_sign_factorization m [axis head j])
  rw [inversion_product_card] at h
  exact h

theorem fixedPositive_card (m : ℕ) : Nat.card (fixedPositive m)=(2^(2*m+1))^12 := by
  have hopp : (fixedPositive m).map
      (MulAut.conj (wordPrefix (step m true) 8)).toMonoidHom ≤ fixedNegative m := by
    rw [eighth_prefix_eq_opposition]
    exact le_of_eq (fixed_positive_image_eq_fixed_negative m)
  have h := card_eq_blocks_of_opposition (fixedPositive m) (fixedNegative m)
    (step m true) 8 (fixed_positive_negative_disjoint m)
    (fun j hj=>simple_block_le_residual m true ⟨j,hj⟩)
    (fun j _=>fixed_sign_factorization m [axis true j]) hopp
  have hw : prefixWeight true 8=12 := by decide +kernel
  rw [inversion_product_card,hw] at h
  exact h

end SymmetricSubgroupAsymptotics.CFSGReeFFourFixedPositiveCardinality
