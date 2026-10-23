import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSectionHeightMembership
import SymmetricSubgroupAsymptotics.CFSGTrialityD4InvariantRoots
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNegativeSimpleRootLine
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylWordAlgebra

/-! Both signs of each literal long section have the claimed original
root label. The negative assertion transports the actual canonical
negative simple subgroup by the same displayed Weyl word. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckSignedSectionMembership
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckSectionRootLabels CFSGTrialityGeckSectionHeightMembership
open CFSGTrialityGeckFixedRootWords CFSGTrialityGeckFixedRootSections
open CFSGTrialityD4PositiveRootIndex CFSGTrialityD4PositiveRootOrbits CFSGTrialityD4InvariantRoots
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
open CFSGNormTwoCoordinateNegativeSimpleRootLine CFSGNormTwoCoordinateRootWeylAction
open CFSGNormTwoGeckWeylWordAlgebra CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoGeckColumns
local notation "A" => CartanMatrix.D 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _

theorem negative_long_word_label (s : Fin 3) :
    CFSGTrialityD4RelativeRootWords.rootWord (longWord s) (negativeRoot (longRoot 0)) =
      negativeRoot (longRoot s) := by
  apply Subtype.ext
  change (wordRoot A hs hp Base Index (longWord s)
    (negativeIndex A hs hp (longRoot 0))).val = (negativeIndex A hs hp (longRoot s)).val
  rw [wordRoot_negative_val,negative_val]
  exact congrArg Neg.neg (congrArg Subtype.val (long_word_label s))

theorem negativeLongSection_mem_root (K : Type) [Field K] (s : Fin 3) (t : K) :
    longSection K s true t ∈ RootLine K (negativeRoot (longRoot s)) := by
  have hx : canonicalRoot rawData K true 1 t ∈ RootLine K (negativeRoot (longRoot 0)) := by
    rw [long_seed_index]
    have he := rootSubgroup_negative_simple_eq_canonical A (CartanMatrix.D_diag 4)
      hs hp (CartanMatrix.D_off_diag_nonpos 4) K 1
    change RootLine K (negativeRoot (Index 1)) = canonicalRootSubgroup rawData K true 1 at he
    rw [he]
    exact ⟨t,rfl⟩
  have hm : canonicalWord rawData K (longWord s) * canonicalRoot rawData K true 1 t *
      (canonicalWord rawData K (longWord s))⁻¹ ∈
      (RootLine K (negativeRoot (longRoot 0))).map
        (MulAut.conj (canonicalWord rawData K (longWord s))).toMonoidHom :=
    ⟨_,hx,rfl⟩
  have he := rootSubgroup_map_word A (CartanMatrix.D_diag 4) hs hp
    (CartanMatrix.D_off_diag_nonpos 4) K (longWord s) (negativeRoot (longRoot 0))
  change (RootLine K (negativeRoot (longRoot 0))).map
      (MulAut.conj (canonicalWord rawData K (longWord s))).toMonoidHom =
    RootLine K (CFSGTrialityD4RelativeRootWords.rootWord (longWord s)
      (negativeRoot (longRoot 0))) at he
  rw [he,negative_long_word_label] at hm
  simpa only [longSection,longTransport_word] using hm

theorem signedLongSection_mem_root (K : Type) [Field K] (neg : Bool) (s : Fin 3) (t : K) :
    longSection K s neg t ∈ RootLine K (signedLongRoot neg s) := by
  cases neg
  · exact longSection_mem_root K s t
  · exact negativeLongSection_mem_root K s t

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckSignedSectionMembership
