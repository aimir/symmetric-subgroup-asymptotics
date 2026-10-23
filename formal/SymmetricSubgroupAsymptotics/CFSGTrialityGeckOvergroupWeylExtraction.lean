import SymmetricSubgroupAsymptotics.CFSGTrialityGeckWeylChamber
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRelativeRootGenerated
import SymmetricSubgroupAsymptotics.CFSGCentralTwistedCommutatorLift
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNegativeRootWordMembership
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortOrbitCommutator
import Mathlib.Tactic.Group

/-! An overgroup containing genuine fixed positive words and a
nonidentity relative Weyl word contains one of the two literal simple
relative Weyl words. Negative parameters are obtained by conjugating
actual fixed parameter-one tests, without a fixed-quotient lift or BN
hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckOvergroupWeylExtraction
open CFSGTrialityGeckWeylChamber CFSGTrialityGeckSimpleOrbitFlags
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityD4WordDiscriminant CFSGTrialityD4InvariantRoots
open CFSGTrialityRelativeWordLanguage CFSGTrialityGeckRelativeRootGenerated
open CFSGTrialityGeckFixedRootWords CFSGTrialityGeckShortParameterWeyl
open CFSGTrialityGeckShortOrbitCommutator CFSGTrialityGeckMatrixTwist
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylWordAlgebra
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoGeckIntegralWord
open CFSGNormTwoRootPairing CFSGNormTwoCoordinateNegativeRootWordMembership
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
open CFSGNormTwoGeckPositivePGroup CFSGCentralTwistedCommutatorLift
local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _

private theorem rootAction_injective (w : List (Fin 4)) : Function.Injective (rootAction w) := by
  intro x y he
  apply Subtype.ext
  apply (linearAction w).injective
  change wordLinear A hs hp Base Index w x.val=wordLinear A hs hp Base Index w y.val
  rw [wordLinear_root,wordLinear_root]
  exact congrArg (fun k : Roots A=>k.val) he

private theorem rootAction_inverse_left (w : List (Fin 4)) (k : Roots A) :
    rootAction w (rootAction (inverseWord w) k)=k := by
  have hlin : linearAction w*linearAction (inverseWord w)=1 := by
    change wordLinear A hs hp Base Index w *
      wordLinear A hs hp Base Index (inverseWord w)=1
    rw [wordLinear_inverseWord,mul_inv_cancel]
  have hk := congrArg (fun L : (Fin 4→ℤ)≃ₗ[ℤ](Fin 4→ℤ)=>L k.val) hlin
  change linearAction w (linearAction (inverseWord w) k.val)=k.val at hk
  apply Subtype.ext
  calc
    _=linearAction w (rootAction (inverseWord w) k).val :=
      (wordLinear_root A hs hp Base Index w (rootAction (inverseWord w) k)).symm
    _=linearAction w (linearAction (inverseWord w) k.val) :=
      congrArg (linearAction w) (wordLinear_root A hs hp Base Index (inverseWord w) k).symm
    _=k.val := hk

private theorem relative_inverse_commutes (r : List (Bool)) (k : Roots A) :
    diagramRoot (rootAction (inverseWord (expandRelative r)) k)=
      rootAction (inverseWord (expandRelative r)) (diagramRoot k) := by
  apply rootAction_injective (expandRelative r)
  rw [←relative_root_action_commutes r,rootAction_inverse_left,rootAction_inverse_left]

private theorem inverse_action_ne_one (w : List (Fin 4)) (hw : linearAction w≠1) :
    linearAction (inverseWord w)≠1 := by
  intro he
  apply hw
  have hh := congrArg (fun L : (Fin 4→ℤ)≃ₗ[ℤ](Fin 4→ℤ)=>linearAction w*L) he
  change wordLinear A hs hp Base Index w *
    wordLinear A hs hp Base Index (inverseWord w)=
    wordLinear A hs hp Base Index w * 1 at hh
  rw [wordLinear_inverseWord,mul_inv_cancel,mul_one] at hh
  exact hh.symm

def orbitParameter (K : Type) [Field K] (sigma : K ≃+* K)
    (neg : Bool) (a : Bool) (t : K) :=
  if a then canonicalRoot rawData K neg 1 t else shortOrbit K sigma neg t

theorem orbitParameter_neg (K : Type) [Field K] (sigma : K ≃+* K)
    (neg a : Bool) (t : K) :
    orbitParameter K sigma neg a (-t) = (orbitParameter K sigma neg a t)⁻¹ := by
  cases a
  · exact shortOrbit_inverse K sigma neg t
  · exact (canonicalRoot_inverse rawData K neg 1 t).symm

theorem orbitParameter_one_fixed (K : Type) [Field K] (sigma : K ≃+* K)
    (neg a : Bool) : unitTwist K sigma (orbitParameter K sigma neg a 1) =
      orbitParameter K sigma neg a 1 := by
  cases a
  · exact shortOrbit_fixed K sigma neg 1 (by simp)
  · change unitTwist K sigma (canonicalRoot rawData K neg 1 1) = _
    rw [CFSGTrialityGeckRootSubgroupTwist.unitTwist_raw_root]
    change canonicalRoot rawData K neg 1 (sigma 1) = canonicalRoot rawData K neg 1 1
    rw [map_one sigma]

theorem orbitParameter_one_mem_signedFixed (K : Type) [Field K] (sigma : K ≃+* K)
    (neg a : Bool) : orbitParameter K sigma neg a 1 ∈ signedFixed K sigma neg := by
  refine ⟨?_,orbitParameter_one_fixed K sigma neg a⟩
  cases a
  · exact shortOrbit_mem_rootGroup K sigma neg 1
  · exact Subgroup.subset_closure ⟨(1,1),rfl⟩

theorem orbit_word_parameter (K : Type) [Field K] (sigma : K ≃+* K) (a : Bool) :
    canonicalWord rawData K (orbitWord a) =
      orbitParameter K sigma false a 1 * orbitParameter K sigma true a (-1) *
        orbitParameter K sigma false a 1 := by
  cases a
  · have he : shortWeylWord K sigma 1 = shortWeyl K := by
      rw [shortWeylWord_eq_product]
      simp only [map_one,CFSGNormTwoGeckWeylSquareTorus.parameterWeyl_one,
        shortWeyl,canonicalWord,mul_one,mul_assoc]
      rfl
    simpa only [shortWeylWord,Units.val_one,inv_one] using he.symm
  · change canonicalWord rawData K [1] = _
    simp only [canonicalWord,canonicalWeyl,mul_one,orbitParameter,if_true]

theorem negative_conjugate_orbit_positive (K : Type) [Field K] (sigma : K ≃+* K)
    (w : List (Fin 4)) (a : Bool)
    (hall : ∀ i ∈ orbitWord a, ∀ j, (rootAction w (Index i)).val j ≤ 0) :
    wordUnit A hs hp Base Index K w * orbitParameter K sigma true a 1 *
      (wordUnit A hs hp Base Index K w)⁻¹ ∈ CFSGTrialityGeckPositiveTwist.Positive K := by
  let W := wordUnit A hs hp Base Index K w
  have hi (i : Fin 4) (him : i ∈ orbitWord a) :
      (MulAut.conj W) (canonicalRoot rawData K true i 1) ∈
        CFSGTrialityGeckPositiveTwist.Positive K :=
    positive_negative_root_word A hd hs hp ho K w i 1 (hall i him)
  change (MulAut.conj W) (orbitParameter K sigma true a 1) ∈ _
  cases a
  · change (MulAut.conj W) (shortOrbit K sigma true 1) ∈ _
    simp only [shortOrbit,map_one,map_mul]
    exact (CFSGTrialityGeckPositiveTwist.Positive K).mul_mem
      ((CFSGTrialityGeckPositiveTwist.Positive K).mul_mem
        (hi 0 (by simp [orbitWord])) (hi 2 (by simp [orbitWord])))
      (hi 3 (by simp [orbitWord]))
  · exact hi 1 (by simp [orbitWord])

theorem exists_negative_orbit_mem (K : Type) [Field K] (sigma : K ≃+* K)
    (H : Subgroup (Matrix GeckIndex GeckIndex K)ˣ)
    (hU : signedFixed K sigma false ≤ H) (r : List Bool)
    (hWmem : wordUnit A hs hp Base Index K (expandRelative r) ∈ H)
    (hne : linearAction (expandRelative r) ≠ 1) :
    ∃ a : Bool, orbitParameter K sigma true a 1 ∈ H := by
  let w := expandRelative r
  let W := wordUnit A hs hp Base Index K w
  obtain ⟨a,hall⟩ := exists_negative_orbit (inverseWord w) (inverse_action_ne_one w hne)
    (relative_inverse_commutes r)
  have hWi : wordUnit A hs hp Base Index K (inverseWord w) = W⁻¹ :=
    wordUnit_inverseWord A hs hp Base Index K w
  let x := W⁻¹ * orbitParameter K sigma true a 1 * W
  have hxpos : x ∈ CFSGTrialityGeckPositiveTwist.Positive K := by
    have hh := negative_conjugate_orbit_positive K sigma (inverseWord w) a hall
    rw [hWi,inv_inv] at hh
    exact hh
  have hWfix : unitTwist K sigma W = W := by
    change unitTwist K sigma (wordUnit A hs hp Base Index K (expandRelative r)) =
      wordUnit A hs hp Base Index K (expandRelative r)
    simpa only [word_eq_canonicalWord] using relative_word_fixed K sigma r
  have hxfix : unitTwist K sigma x = x := by
    change unitTwist K sigma (W⁻¹ * orbitParameter K sigma true a 1 * W) = _
    rw [map_mul,map_mul,map_inv,hWfix,orbitParameter_one_fixed]
  have hxH : x ∈ H := hU ⟨hxpos,hxfix⟩
  have hh : W*x*W⁻¹ ∈ H := H.mul_mem (H.mul_mem hWmem hxH) (H.inv_mem hWmem)
  have he : W*x*W⁻¹ = orbitParameter K sigma true a 1 := by dsimp only [x]; group
  exact ⟨a,he ▸ hh⟩

theorem exists_simple_weyl_mem (K : Type) [Field K] (sigma : K ≃+* K)
    (H : Subgroup (Matrix GeckIndex GeckIndex K)ˣ)
    (hU : signedFixed K sigma false ≤ H) (r : List Bool)
    (hWmem : wordUnit A hs hp Base Index K (expandRelative r) ∈ H)
    (hne : linearAction (expandRelative r) ≠ 1) :
    ∃ a : Bool, canonicalWord rawData K (orbitWord a) ∈ H := by
  obtain ⟨a,ha⟩ := exists_negative_orbit_mem K sigma H hU r hWmem hne
  have hpH := hU (orbitParameter_one_mem_signedFixed K sigma false a)
  have hnH : orbitParameter K sigma true a (-1) ∈ H := by
    rw [orbitParameter_neg]
    exact H.inv_mem ha
  refine ⟨a,?_⟩
  rw [orbit_word_parameter]
  exact H.mul_mem (H.mul_mem hpH hnH) hpH

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckOvergroupWeylExtraction
