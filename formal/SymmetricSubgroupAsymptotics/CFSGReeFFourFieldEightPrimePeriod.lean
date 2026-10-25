import SymmetricSubgroupAsymptotics.PrimePeriodSimpleQuotientIndex
import SymmetricSubgroupAsymptotics.CFSGFFourE6NormMatrixNegativeAction
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalMiddleParabolic
import Mathlib.Tactic.NormNum

/-! The actual 26-dimensional folded action is tied to the same original
Ree F4 quotient. A selected vector of period 109 would yield the needed
proper-index bound; no such word or vector is asserted in this module. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightPrimePeriod
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGFFourOriginalFoldedEquivalence CFSGFFourE6CharacteristicTwoNormImage
open CFSGReeFFourPerfectProjection CFSGReeFFourFixedAmbientHom
open CFSGReeFFourOriginalMiddleParabolic CFSGReeFFourFixedBorelCardinality

private instance fixedFinite (m : ℕ) : Finite (originalModelFixed m) :=
  Finite.of_injective (fixedAmbientHom m) (fixedAmbientHom_injective m)

private instance originalFinite : Finite (CFSG.Models.ReeF4 1) :=
  Finite.of_surjective (fixedToOriginal 1 (by omega))
    (fixedToOriginal_surjective 1 (by omega))

def fixedNormAction (m : ℕ) : originalModelFixed m →*
    (characteristicNormImage (Field m) ≃ₗ[Field m] characteristicNormImage (Field m)) :=
  (normAction (Field m)).comp
    ((modelEquivFolded (Field m)).toMonoidHom.comp (originalModelFixed m).subtype)

theorem quotient_kernel_le_borel :
    (fixedToOriginal 1 (by omega)).ker ≤ fixedBorel 1 :=
  (fixedToOriginal_kernel_le_center 1 (by omega)).trans (center_le_borel 1)

theorem proper_index_of_selected_period
    [IsSimpleGroup (CFSG.Models.ReeF4 1)]
    (g : originalModelFixed 1) (v : characteristicNormImage (Field 1))
    (hperiod : fixedNormAction 1 (g^109) v = v)
    (hmoved : fixedNormAction 1 g v ≠ v)
    (H : Subgroup (CFSG.Models.ReeF4 1)) (hH : H ≠ ⊤) : 109 ≤ H.index := by
  letI : MulAction (originalModelFixed 1) (characteristicNormImage (Field 1)) :=
    MulAction.compHom _ (fixedNormAction 1)
  apply PrimePeriodSimpleQuotientIndex.prime_le_proper_index_of_point_period
    109 (by decide +kernel) (fixedToOriginal 1 (by omega))
    (fixedToOriginal_surjective 1 (by omega)) (fixedBorel 1) quotient_kernel_le_borel
    ?_ g v hperiod hmoved H hH
  rw [fixedBorel_card]
  norm_num

end SymmetricSubgroupAsymptotics.CFSGReeFFourFieldEightPrimePeriod
