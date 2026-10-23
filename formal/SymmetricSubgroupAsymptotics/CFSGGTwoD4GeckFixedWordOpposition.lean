import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedWordSimpleSigns
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOvergroupWeylExtraction
import SymmetricSubgroupAsymptotics.CFSGFixedSubgroupConjugation

/-! Identity-field-twist disjoint positive groups force an opposite
relative Weyl cell. Both tests are actual fixed parameter-one words;
neither ambient disjointness nor a BN-pair is assumed. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckFixedWordOpposition
open CFSGTrialityGeckRelativeSimpleSigns CFSGTrialityGeckShortCentralizerCardinality
open CFSGTrialityGeckFixedRootWords CFSGTrialityGeckShortOrbitCommutator
open CFSGTrialityGeckDiagramCovariance CFSGTrialityD4NormTwo CFSGTrialityRelativeWordLanguage
open CFSGTrialityD4WordDiscriminant
open CFSGTrialityGeckRelativeRootGenerated CFSGTrialityGeckPositiveTwist
open CFSGTrialityGeckNormalizerEnvelope
open CFSGTrialityGeckMatrixTwist CFSGTrialityGeckOvergroupWeylExtraction
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckIntegralRealization
open CFSGNormTwoCoordinateWeylRootMembership CFSGNormTwoGeckIntegralWord
open CFSGNormTwoCoordinateNegativeSimpleWord CFSGNormTwoCoordinateHeight
open CFSGNormTwoGeckOppositeIntersection CFSGSerreQuadraticMatrix
open CFSGCentralTwistedCommutatorLift CFSGFixedSubgroupConjugation
local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _
variable (K : Type) [Field K] [Finite K]

theorem word_fixed (r : List Bool) :
    unitTwist K (RingEquiv.refl K) (wordUnit A hs hp Base Index K (expandRelative r)) =
      wordUnit A hs hp Base Index K (expandRelative r) := by
  rw [word_eq_canonicalWord]
  exact CFSGTrialityRelativeWordLanguage.relative_word_fixed K (RingEquiv.refl K) r

private theorem conjugate_mem_fixed (r : List Bool) (x : (Matrix GeckIndex GeckIndex K)ˣ)
    (hx : x ∈ signedFixed K (RingEquiv.refl K) false)
    (hpos : wordUnit A hs hp Base Index K (expandRelative r) * x *
      (wordUnit A hs hp Base Index K (expandRelative r))⁻¹ ∈ Positive K) :
    wordUnit A hs hp Base Index K (expandRelative r) * x *
      (wordUnit A hs hp Base Index K (expandRelative r))⁻¹ ∈
        signedFixed K (RingEquiv.refl K) false := by
  refine ⟨hpos, ?_⟩
  have hxfix : unitTwist K (RingEquiv.refl K) x = x := hx.2
  change unitTwist K (RingEquiv.refl K)
      (wordUnit A hs hp Base Index K (expandRelative r) * x *
        (wordUnit A hs hp Base Index K (expandRelative r))⁻¹) = _
  rw [map_mul, map_mul, map_inv, word_fixed, hxfix]

private theorem source_eq_one_of_disjoint {G : Type*} [Group G]
    (H : Subgroup G) (g x : G) (hx : x ∈ H) (hgx : g * x * g⁻¹ ∈ H)
    (hdisjoint : H ⊓ H.map (MulAut.conj g).toMonoidHom = ⊥) : x = 1 := by
  have hm : g * x * g⁻¹ ∈ H ⊓ H.map (MulAut.conj g).toMonoidHom := ⟨hgx, ⟨x, hx, rfl⟩⟩
  rw [hdisjoint, Subgroup.mem_bot] at hm
  apply (MulAut.conj g).injective
  exact hm.trans (map_one (MulAut.conj g)).symm

private theorem positive_conjugate_short (r : List Bool)
    (hpos : ∀ i, 0 ≤ (rootAction (expandRelative r) (Index 0)).val i) :
    wordUnit A hs hp Base Index K (expandRelative r) *
      shortOrbit K (RingEquiv.refl K) false 1 *
        (wordUnit A hs hp Base Index K (expandRelative r))⁻¹ ∈ Positive K := by
  let W := wordUnit A hs hp Base Index K (expandRelative r)
  have hall := relative_outer_images_nonnegative r hpos
  change (MulAut.conj W) (shortOrbit K (RingEquiv.refl K) false 1) ∈ _
  change (MulAut.conj W) (CFSGSerreQuadraticMatrix.canonicalRoot rawData K false 0 1 *
    CFSGSerreQuadraticMatrix.canonicalRoot rawData K false 2 1 *
    CFSGSerreQuadraticMatrix.canonicalRoot rawData K false 3 1) ∈ _
  rw [map_mul, map_mul]
  exact (Positive K).mul_mem ((Positive K).mul_mem
    (positive_word_mem A hd hs hp ho K (expandRelative r) 0 1 (hall 0 (by decide)))
    (positive_word_mem A hd hs hp ho K (expandRelative r) 2 1 (hall 2 (by decide))))
    (positive_word_mem A hd hs hp ho K (expandRelative r) 3 1 (hall 3 (by decide)))

theorem relative_simple_nonpositive_of_fixed_disjoint (r : List Bool)
    (hdisj : signedFixed K (RingEquiv.refl K) false ⊓
      (signedFixed K (RingEquiv.refl K) false).map
        (MulAut.conj (wordUnit A hs hp Base Index K (expandRelative r))).toMonoidHom = ⊥)
    (i : Fin 4) : ∀ l, (rootAction (expandRelative r) (Index i)).val l ≤ 0 := by
  let W := wordUnit A hs hp Base Index K (expandRelative r)
  have hshort : shortOrbit K (RingEquiv.refl K) false 1 ∈
      signedFixed K (RingEquiv.refl K) false :=
    orbitParameter_one_mem_signedFixed K (RingEquiv.refl K) false false
  have hmiddle : CFSGSerreQuadraticMatrix.canonicalRoot rawData K false 1 1 ∈
      signedFixed K (RingEquiv.refl K) false :=
    orbitParameter_one_mem_signedFixed K (RingEquiv.refl K) false true
  have h0 : ∀ l, (rootAction (expandRelative r) (Index 0)).val l ≤ 0 := by
    rcases word_sign_membership A hd hs hp ho K (expandRelative r) 0 1 with hpos | hneg
    · have hconj := conjugate_mem_fixed K r _ hshort (positive_conjugate_short K r hpos.1)
      have he := source_eq_one_of_disjoint _ W _ hshort hconj hdisj
      have hz := shortOrbit_injective K (RingEquiv.refl K)
        (he.trans (shortOrbit_zero K (RingEquiv.refl K) false).symm)
      exact False.elim (one_ne_zero hz)
    · exact hneg.1
  have h1 : ∀ l, (rootAction (expandRelative r) (Index 1)).val l ≤ 0 := by
    rcases word_sign_membership A hd hs hp ho K (expandRelative r) 1 1 with hpos | hneg
    · have hconj := conjugate_mem_fixed K r _ hmiddle hpos.2
      have he := source_eq_one_of_disjoint _ W _ hmiddle hconj hdisj
      exact False.elim (canonicalRoot_one_ne_one A hs hp Base Index coordinateHeight
        (simple_height A hd hs hp ho) K 1 he)
    · exact hneg.1
  exact relative_simple_images_nonpositive r h0 h1 i

theorem fixed_positive_image_eq_negative_of_disjoint (r : List Bool)
    (hdisj : signedFixed K (RingEquiv.refl K) false ⊓
      (signedFixed K (RingEquiv.refl K) false).map
        (MulAut.conj (wordUnit A hs hp Base Index K (expandRelative r))).toMonoidHom = ⊥) :
    (signedFixed K (RingEquiv.refl K) false).map
      (MulAut.conj (wordUnit A hs hp Base Index K (expandRelative r))).toMonoidHom =
        signedFixed K (RingEquiv.refl K) true := by
  have hpos : (Positive K).map
      (MulAut.conj (wordUnit A hs hp Base Index K (expandRelative r))).toMonoidHom = Negative K :=
    positive_map_eq_negative_of_simple_nonpositive A hd hs hp ho K (expandRelative r)
      (relative_simple_nonpositive_of_fixed_disjoint K r hdisj)
  change (Positive K ⊓ fixedSubgroup (unitTwist K (RingEquiv.refl K))).map _ = _
  rw [map_inf_fixed _ _ _ (word_fixed K r), hpos]
  rfl

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckFixedWordOpposition
