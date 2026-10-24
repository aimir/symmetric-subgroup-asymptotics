import SymmetricSubgroupAsymptotics.CFSGReeFFourPositiveBlockConjugation
import SymmetricSubgroupAsymptotics.CFSGReeFFourSimpleInversionBlocks

/-! Finite integral signs imply conjugate positivity of the whole actual
fixed inversion block. Actual ordinary-source parameter coverage is
used on each block before applying the faithful ambient homomorphism. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFixedBlockConjugation
open CFSGReeFFourPositiveBlockConjugation CFSGReeFFourPositiveMatrixWordValues
open CFSGReeFFourSimpleInversionBlocks CFSGReeFFourFixedBruhatCover
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourOuterFixedInversion CFSGReeFFourMiddleFixedInversion
open CFSGReeFFourMiddleFixedSubgroup CFSGReeFFourOuterFixedRoot
open CFSGReeFFourFieldParameters CFSGFFourOriginalMiddleWords
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoRootPairing
open CFSGTwistedE6GeckPositiveTwist CFSGExceptionalCartanPositiveDefinite
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem middle_block_conjugate_le (m : ℕ) (g : originalModelFixed m)
    (v : List (Fin 6))
    (hg : fixedRawHom m g=wordUnit A hs hp b₀ s₀ (Field m) v)
    (hpos : positiveBlockSigns true v) :
    (fixedMiddleInversion m).map (MulAut.conj g).toMonoidHom ≤ fixedPositive m := by
  rintro _ ⟨x,hx,rfl⟩
  rw [fixedMiddleInversion_eq_middleFixedSubgroup] at hx
  obtain ⟨a,b,c,d,hx⟩ := hx
  have hval : fixedRawHom m x=coordinateMiddleWord m a b c d := by
    rw [fixedRawHom_apply,←hx]
    exact rawHom_middleWord_eq_coordinate m a b c d
  change fixedRawHom m (g*x*g⁻¹)∈Positive (Field m)
  rw [map_mul,map_mul,map_inv,hg,hval]
  exact coordinateMiddleWord_conjugate_mem m v hpos a b c d

theorem outer_block_conjugate_le (m : ℕ) (g : originalModelFixed m)
    (v : List (Fin 6))
    (hg : fixedRawHom m g=wordUnit A hs hp b₀ s₀ (Field m) v)
    (hpos : positiveBlockSigns false v) :
    (fixedOuterInversion m).map (MulAut.conj g).toMonoidHom ≤ fixedPositive m := by
  rintro _ ⟨x,hx,rfl⟩
  rw [fixedOuterInversion_eq_range] at hx
  obtain ⟨a,ha⟩ := hx
  have hval : fixedRawHom m x=coordinateOuterWord m a.toAdd := by
    rw [←ha,fixedRawHom_apply]
    exact rawHom_outerWord_eq_coordinate m a.toAdd
  change fixedRawHom m (g*x*g⁻¹)∈Positive (Field m)
  rw [map_mul,map_mul,map_inv,hg,hval]
  exact coordinateOuterWord_conjugate_mem m v hpos a.toAdd

end SymmetricSubgroupAsymptotics.CFSGReeFFourFixedBlockConjugation
