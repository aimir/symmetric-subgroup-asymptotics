import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalMixedA2Rigidity
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootWeylAction
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalComplementNormalizer

/-! The selected negative simple parameters have exactly the literal
canonical negative simple subgroup as their range, through the SAME
original projection. The comparison uses the proved Weyl reflection. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNegativeSimpleRootLine
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoCoordinateOriginalProjection
open CFSGNormTwoCoordinateOriginalRootDegree CFSGNormTwoCoordinatePositivePairCollecting
open CFSGNormTwoCoordinateElementaryRootParameters CFSGRootParameterAutomorphism
open CFSGFieldScaledRootHom CFSGCommutatorParameterRange
open CFSGNormTwoCoordinateOriginalA2FieldRecognition
open CFSGNormTwoCoordinateOriginalA2PairStabilizer
open CFSGNormTwoCoordinateOriginalAllRootLines CFSGNormTwoCoordinateRootElementRange
open CFSGNormTwoCoordinateRootSubgroup
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i, A i i = 2)
    (hs : A.transpose = A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j, i ≠ j → A i j ≤ 0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

open CFSGNormTwoCoordinateOriginalSimpleParameters CFSGNormTwoCoordinateWordPairCollecting
open CFSGNormTwoGeckWeylWordDegree

open CFSGNormTwoCoordinateOriginalSignedParameters CFSGNormTwoCoordinateA2ReflectionLabels
open CFSGCommutatorParameterRigidity CFSGNormTwoGeckColumns

open CFSGNormTwoCoordinateCanonicalSimpleRootLine CFSGNormTwoCoordinateRootWeylAction
open CFSGNormTwoGeckSelfRootConjugation CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoCoordinateOriginalComplementNormalizer
open CFSGNormTwoGeckIntegralWord
open CFSGSerreQuadraticWeylWord
open CFSGNormTwoCoordinateOriginalMixedA2Rigidity
local notation "D" => realizationData A hs hp b₀ s₀

theorem rootSubgroup_negative_simple_eq_canonical (j : Fin r) :
    rootSubgroup A hd hs hp ho K (negativeIndex A hs hp (s₀ j)) =
      canonicalRootSubgroup D K true j := by
  have he := rootSubgroup_map_word A hd hs hp ho K [j] (s₀ j)
  rw [rootSubgroup_simple_eq_canonical A hd hs hp ho K j,
    reflect_simple_self A hd hs hp ho j] at he
  rw [← he]
  simp only [canonicalWord, mul_one]
  apply Subgroup.ext
  intro x
  constructor
  · rintro ⟨y, ⟨a, rfl⟩, rfl⟩
    refine ⟨-a, ?_⟩
    exact (self_root_word A hs hp b₀ s₀ K j a).symm
  · rintro ⟨a, rfl⟩
    refine ⟨canonicalRoot D K false j (-a), ⟨-a, rfl⟩, ?_⟩
    simpa only [neg_neg] using self_root_word A hs hp b₀ s₀ K j (-a)

 theorem negativeParameterHom_range [Finite K] [Nontrivial (Fin r)]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i j : Fin r) :
    (negativeParameterHom A hd hs hp ho K i j).range =
      originalNegativeSimpleRootGroup A hd hs hp ho K i j := by
  rw [negativeParameterHom, rootParameterHom_range]
  change ((rootSubgroup A hd hs hp ho K (negativeIndex A hs hp (s₀ j))).subgroupOf
    (ElementaryGroup A hd hs hp ho K)).map (originalProjection A hd hs hp ho K i) = _
  rw [rootSubgroup_negative_simple_eq_canonical A hd hs hp ho K j]
  rfl

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNegativeSimpleRootLine
