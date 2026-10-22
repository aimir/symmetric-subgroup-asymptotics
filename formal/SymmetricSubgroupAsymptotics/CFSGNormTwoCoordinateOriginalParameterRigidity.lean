import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNegativeSimpleRootLine

/-! Actual original automorphisms are determined by their positive
simple-root parameters once the negative simple subgroups are preserved.
Mixed A2 incidence fixes the negative parameters, and the SAME elementary
root generation plus surjective originalProjection fixes the whole group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalParameterRigidity
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
open CFSGNormTwoCoordinateOriginalMixedA2Rigidity
local notation "D" => realizationData A hs hp b₀ s₀

open CFSGNormTwoCoordinateNegativeSimpleRootLine CFSGNormTwoCoordinateOriginalNormalizerIntersection

theorem eq_one_of_all_simple_parameters_fixed [Finite K] [Nontrivial (Fin r)]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r)
    (f : MulAut (Projective (cartan b₀ s₀) K))
    (hpos : ∀ j a, f (simpleParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd a)) =
      simpleParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd a))
    (hneg : ∀ j a, f (negativeParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd a)) =
      negativeParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd a)) : f = 1 := by
  let π := originalProjection A hd hs hp ho K i
  have hhom : f.toMonoidHom.comp π = π := by
    apply MonoidHom.eq_of_eqOn_dense
      (CFSGSerreSquareZeroMatrix.elementaryRootSet_generate K (canonicalRoot D K))
    rintro x ⟨neg, j, t, rfl⟩
    change f (π (canonicalElementaryRoot D K neg j t)) = π (canonicalElementaryRoot D K neg j t)
    cases neg
    · have hx : π (canonicalElementaryRoot D K false j t) ∈
          originalSimpleRootGroup A hd hs hp ho K i j :=
        ⟨canonicalElementaryRoot D K false j t, ⟨t, rfl⟩, rfl⟩
      rw [originalSimpleRootGroup_eq_fullRootLine A hd hs hp ho K i j,
        ← simpleParameterHom_range A hd hs hp ho K i j] at hx
      obtain ⟨a, ha⟩ := hx
      rw [← ha]
      exact hpos j a.toAdd
    · have hx : π (canonicalElementaryRoot D K true j t) ∈
          originalNegativeSimpleRootGroup A hd hs hp ho K i j :=
        ⟨canonicalElementaryRoot D K true j t, ⟨t, rfl⟩, rfl⟩
      rw [← negativeParameterHom_range A hd hs hp ho K i j] at hx
      obtain ⟨a, ha⟩ := hx
      rw [← ha]
      exact hneg j a.toAdd
  ext x
  obtain ⟨y, rfl⟩ := originalProjection_surjective A hd hs hp ho K i x
  exact DFunLike.congr_fun hhom y

 theorem eq_one_of_positive_parameters_fixed [Finite K] [Nontrivial (Fin r)]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r)
    (hneighbors : ∀ j, ∃ k, A j k = -1)
    (f : MulAut (Projective (cartan b₀ s₀) K))
    (hpos : ∀ j a, f (simpleParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd a)) =
      simpleParameterHom A hd hs hp ho K i j (Multiplicative.ofAdd a))
    (hneg : ∀ j, (originalNegativeSimpleRootGroup A hd hs hp ho K i j).map f.toMonoidHom =
      originalNegativeSimpleRootGroup A hd hs hp ho K i j) : f = 1 := by
  apply eq_one_of_all_simple_parameters_fixed A hd hs hp ho K i f hpos
  intro j
  obtain ⟨k, hjk⟩ := hneighbors j
  apply negative_simple_parameter_fixed A hd hs hp ho K p i j k hjk f (hpos j) (hpos k)
  simpa only [negativeParameterHom_range] using hneg j

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalParameterRigidity
