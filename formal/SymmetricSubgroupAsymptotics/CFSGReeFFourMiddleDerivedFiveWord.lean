import SymmetricSubgroupAsymptotics.FourCycleInvolutionFiveProduct
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleFixedLaw
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleWeylConstantWord
import SymmetricSubgroupAsymptotics.CFSGReeFFourRelativeWeylInvolutions
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleParabolicCardinality

/-! A literal order-five word in the derived fixed group, for every m.
It is obtained from the checked middle multiplication and constant Weyl
identity. No Suzuki recognition, known group order, or claim that this
odd-order word survives the full derived-centre quotient is made. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleDerivedFiveWord
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourMiddleFixedWords CFSGReeFFourMiddleFixedLaw
open CFSGReeFFourMiddleWordMultiplication CFSGReeFFourMiddleFixedSubgroup
open CFSGReeFFourMiddleWeylConstantWord CFSGReeFFourRelativeWeylInvolutions
open CFSGReeFFourRelativeSimpleWeyl CFSGReeFFourRelativePositiveSubgroups
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourFixedBorelCardinality
open CFSGReeFFourMiddleParabolicCardinality FourCycleInvolutionFiveProduct
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem parameter_zero (m : ℕ) : fixedMiddleParameter m (0,0) = 1 := by
  apply Subtype.ext
  change fixedMiddleWord m 0 0 = 1
  simpa only [fixedMiddleWord, map_zero, zero_pow (by decide : 2 ≠ 0),
    zero_mul, add_zero] using middleWord_zero m

def fourCycle (m : ℕ) : originalModelFixed m := fixedMiddleParameter m (1,0)

theorem fourCycle_square (m : ℕ) :
    (fourCycle m)^2 = fixedMiddleParameter m (0,1) := by
  rw [pow_two]
  change fixedMiddleParameter m (1,0)*fixedMiddleParameter m (1,0) = _
  simpa only [map_one, CharTwo.add_self_eq_zero, zero_add, one_mul] using
    fixedMiddleParameter_mul m 1 0 1 0

theorem fourCycle_cube (m : ℕ) :
    (fourCycle m)^3 = fixedMiddleParameter m (1,1) := by
  rw [pow_succ, fourCycle_square]
  change fixedMiddleParameter m (0,1)*fixedMiddleParameter m (1,0) = _
  simpa only [map_zero, zero_add, add_zero, mul_zero] using
    fixedMiddleParameter_mul m 0 1 1 0

theorem fourCycle_four (m : ℕ) : (fourCycle m)^4 = 1 := by
  have hz : (fixedMiddleParameter m (0,1))^2 = 1 := by
    rw [pow_two, fixedMiddleParameter_mul]
    simpa only [map_zero, zero_add, CharTwo.add_self_eq_zero, zero_mul, add_zero] using
      parameter_zero m
  rw [← fourCycle_square] at hz
  simpa only [← pow_mul] using hz

theorem middleWeyl_square (m : ℕ) : (middleFixedWeyl m)^2 = 1 := by
  have hi : (middleFixedWeyl m)⁻¹ = middleFixedWeyl m :=
    Subtype.ext (middleRelativeWeyl_inv m)
  rw [pow_two]
  calc
    _ = middleFixedWeyl m*(middleFixedWeyl m)⁻¹ := by rw [hi]
    _ = 1 := mul_inv_cancel _

theorem constant_word (m : ℕ) :
    middleFixedWeyl m = (fourCycle m)^2 *
      (middleFixedWeyl m*fourCycle m*(middleFixedWeyl m)⁻¹) * (fourCycle m)^3 := by
  rw [fourCycle_square, fourCycle_cube]
  apply Subtype.ext
  exact middleRelativeWeyl_constant_factors m

def fiveWord (m : ℕ) : originalModelFixed m := middleFixedWeyl m*(fourCycle m)^2

theorem fiveWord_conjugate (m : ℕ) :
    fourCycle m*fiveWord m*(fourCycle m)⁻¹ = (fiveWord m)^2 :=
  conjugate_product (fourCycle m) (middleFixedWeyl m)
    (shift_of_constant_word _ _ (fourCycle_four m) (middleWeyl_square m) (constant_word m))

theorem fiveWord_pow_five (m : ℕ) : (fiveWord m)^5 = 1 :=
  product_pow_five (fourCycle m) (middleFixedWeyl m) (fourCycle_four m)
    (middleWeyl_square m)
    (shift_of_constant_word _ _ (fourCycle_four m) (middleWeyl_square m) (constant_word m))

theorem fiveWord_mem_commutator (m : ℕ) : fiveWord m ∈ commutator (originalModelFixed m) :=
  product_mem_commutator (fourCycle m) (middleFixedWeyl m)
    (shift_of_constant_word _ _ (fourCycle_four m) (middleWeyl_square m) (constant_word m))

theorem fiveWord_ne_one (m : ℕ) : fiveWord m ≠ 1 := by
  intro he
  have hw : middleFixedWeyl m = ((fourCycle m)^2)⁻¹ := by
    calc
      _ = fiveWord m*((fourCycle m)^2)⁻¹ := by dsimp only [fiveWord]; group
      _ = _ := by rw [he, one_mul]
  apply middleFixedWeyl_not_mem_borel m
  apply positive_le_borel m
  rw [hw]
  apply (fixedPositive m).inv_mem
  rw [fourCycle_square]
  exact middleFixedSubgroup_le_fixedPositive m
    ⟨0, alpha m 0, 1, alpha m 1 + 0^2*alpha m 0, rfl⟩

theorem fiveWord_order (m : ℕ) : orderOf (fiveWord m) = 5 :=
  orderOf_eq_prime (fiveWord_pow_five m) (fiveWord_ne_one m)

def derivedFiveWord (m : ℕ) : commutator (originalModelFixed m) :=
  ⟨fiveWord m, fiveWord_mem_commutator m⟩

theorem derivedFiveWord_order (m : ℕ) : orderOf (derivedFiveWord m) = 5 :=
  (orderOf_injective (commutator (originalModelFixed m)).subtype
    Subtype.val_injective (derivedFiveWord m)).symm.trans (fiveWord_order m)

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleDerivedFiveWord
