import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCentralExtensionData
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckGeneratedOriginalProjection
import SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex

/-! The actual fixed middle radical injects into the SAME original
triality central quotient. Motion of one nontrivial highest-root element
therefore forces the sharp prime-times-q^4 proper-index bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddlePairingIndex

open CFSGTrialityMiddleFixedTensorSpan CFSGTrialityMiddleFixedTensorCardinality
open CFSGTrialityGeckMiddleFixedCommutators CFSGTrialityGeckMiddleFixedCentralParameters
open CFSGTrialityGeckMiddleCentralExtensionData CFSGTrialityGeckFixedPositiveRaw
open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckPositiveTwist
open CFSGTrialityGeckFixedPositiveGeneration CFSGTrialityGeckPositiveDerivedEquiv
open CFSGTrialityGeckOriginalIndexSquare CFSGTrialityGeckOriginalRootFamily
open CFSGTrialityGeckGeneratedOriginalProjection CFSGSerreOrdinaryTwists
open PrimitiveSocleRawStructure
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance
local instance (q : CFSG.PrimePower) : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
local instance (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    Finite (CFSG.Models.TrialityD4 q) :=
  Finite.of_surjective (generatedToOriginal q) (generatedToOriginal_surjective q)

private def middleToPositive (q : CFSG.PrimePower) : fixedMiddle q →*
    fixedPositive (K q) (definingFieldAutomorphism q 3) where
  toFun u := by
    let h := (mem_fixedPositiveRaw_iff q u.val).mp u.property.2
    refine ⟨⟨u.val,h.1⟩,?_⟩
    apply Subtype.ext
    exact (positiveTwist_val (K q) (definingFieldAutomorphism q 3) ⟨u.val,h.1⟩).trans h.2
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem middleToPositive_injective (q : CFSG.PrimePower) :
    Function.Injective (middleToPositive q) := by
  intro u v he
  exact Subtype.ext (congrArg (fun x : fixedPositive (K q) (definingFieldAutomorphism q 3) => x.val.val) he)

def originalMiddle (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    fixedMiddle q →* CFSG.Models.TrialityD4 q :=
  ((originalProjection q).comp
    (CFSGTrialityGeckFixedPositiveImageSylow.imagePositiveSylow q :
      Subgroup (CFSGTrialityGeckFixedPositiveImageSylow.DerivedImage q)).subtype).comp
    ((positiveEquivSylow q).toMonoidHom.comp (middleToPositive q))

theorem originalMiddle_injective (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] : Function.Injective (originalMiddle q) :=
  (originalProjection_sylow_injective q).comp
    ((positiveEquivSylow q).injective.comp (middleToPositive_injective q))

theorem original_central_one_ne_one (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    originalMiddle q (central q (Multiplicative.ofAdd (1 : F q))) ≠ 1 := by
  intro he
  have he' := originalMiddle_injective q (he.trans (map_one (originalMiddle q)).symm)
  have hc := central_injective q (he'.trans (map_one (central q)).symm)
  have hz : (1 : F q) = 0 := congrArg Multiplicative.toAdd hc
  exact one_ne_zero hz

theorem typeTriality_middle_le_proper_index (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)]
    (H : Subgroup (CFSG.Models.TrialityD4 q)) (hH : H ≠ ⊤) :
    q.prime*q.order^4 ≤ H.index := by
  obtain ⟨x,hx⟩ := CFSGConjugateSubgroupDegree.exists_moved_coset_of_ne_one H hH
    (originalMiddle q (central q (Multiplicative.ofAdd (1 : F q))))
    (original_central_one_ne_one q)
  letI : MulAction (fixedMiddle q) (CFSG.Models.TrialityD4 q ⧸ H) :=
    MulAction.compHom _ (originalMiddle q)
  have hd := (extensionData q).degree_le_of_central_motion q.prime 4
    (by rw [fullEnvelope_finrank]) x (Multiplicative.ofAdd (1 : F q)) hx
  rw [CFSGTrialityFixedField.fixedField_card] at hd
  exact hd

theorem typeTriality_middle_le_leastProperIndex (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.TrialityD4 q) ell) : q.prime*q.order^4 ≤ ell := by
  obtain ⟨H,hH,he⟩ := hell.1
  rw [←he]
  exact typeTriality_middle_le_proper_index q H hH

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddlePairingIndex
