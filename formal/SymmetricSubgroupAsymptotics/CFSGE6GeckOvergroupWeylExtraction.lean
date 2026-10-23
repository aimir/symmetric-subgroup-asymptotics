import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNegativeRootWordMembership
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedWordSimpleSigns
import Mathlib.Tactic.Group

/-! A subgroup containing the ACTUAL fixed E6 upper group and a relative
Weyl word with nonidentity lattice action contains an actual folded
simple Weyl word. Inverse chamber descent finds the simple orbit, and
literal negative-root conjugation puts its opposite parameter-one element
in the subgroup. No centre or folded abelianization recognition is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckOvergroupWeylExtraction
open CFSGTwistedE6WeylChamber CFSGTwistedE6RelativeWeylOrbits
open CFSGTwistedE6FixedWordClassification CFSGTwistedE6GeckRelativeRootGenerated
open CFSGTwistedE6GeckFixedSimpleTests CFSGTwistedE6GeckRelativeWordTwist
open CFSGTwistedE6GeckMatrixTwist CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6GeckDiagramCovariance CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGNormTwoRootPairing
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylWordAlgebra
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoGeckIntegralWord
open CFSGNormTwoGeckOrthogonalWeyl CFSGNormTwoCoordinateNegativeRootWordMembership
open CFSGSerreQuadraticMatrix
open CFSGSerreQuadraticWeylWord
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

theorem rootAction_injective (w : List (Fin 6)) : Function.Injective (rootAction w) := by
  intro x y he
  apply Subtype.ext
  apply (linearAction w).injective
  change wordLinear A hs hp E6Base E6Index w x.val=wordLinear A hs hp E6Base E6Index w y.val
  rw [wordLinear_root,wordLinear_root]
  exact congrArg (fun k : Roots A=>k.val) he

theorem rootAction_inverse_left (w : List (Fin 6)) (k : Roots A) :
    rootAction w (rootAction (inverseWord w) k)=k := by
  have hlin : linearAction w*linearAction (inverseWord w)=1 := by
    change wordLinear A hs hp E6Base E6Index w *
      wordLinear A hs hp E6Base E6Index (inverseWord w)=1
    rw [wordLinear_inverseWord,mul_inv_cancel]
  have hk := congrArg (fun L : (Fin 6→ℤ)≃ₗ[ℤ](Fin 6→ℤ)=>L k.val) hlin
  change linearAction w (linearAction (inverseWord w) k.val)=k.val at hk
  apply Subtype.ext
  calc
    _=linearAction w (rootAction (inverseWord w) k).val :=
      (wordLinear_root A hs hp E6Base E6Index w (rootAction (inverseWord w) k)).symm
    _=linearAction w (linearAction (inverseWord w) k.val) :=
      congrArg (linearAction w) (wordLinear_root A hs hp E6Base E6Index (inverseWord w) k).symm
    _=k.val := hk

theorem relative_inverse_commutes (r : List (Fin 4)) (k : Roots A) :
    diagramRoot (rootAction (inverseWord (expandRelative r)) k)=
      rootAction (inverseWord (expandRelative r)) (diagramRoot k) := by
  apply rootAction_injective (expandRelative r)
  rw [←relative_root_action_commutes r,rootAction_inverse_left,rootAction_inverse_left]

theorem inverse_action_ne_one (w : List (Fin 6)) (hw : linearAction w≠1) :
    linearAction (inverseWord w)≠1 := by
  intro he
  apply hw
  have hh := congrArg (fun L : (Fin 6→ℤ)≃ₗ[ℤ](Fin 6→ℤ)=>linearAction w*L) he
  change wordLinear A hs hp E6Base E6Index w *
    wordLinear A hs hp E6Base E6Index (inverseWord w)=
    wordLinear A hs hp E6Base E6Index w * 1 at hh
  rw [wordLinear_inverseWord,mul_inv_cancel,mul_one] at hh
  exact hh.symm

theorem negative_conjugate_orbit_positive (K : Type) [Field K] (w : List (Fin 6)) (a : Fin 4)
    (hall : ∀i∈orbitWord a,∀j,(rootAction w (E6Index i)).val j≤0) :
    wordUnit A hs hp E6Base E6Index K w*orbitParameter K true a 1*
      (wordUnit A hs hp E6Base E6Index K w)⁻¹∈Positive K := by
  let W := wordUnit A hs hp E6Base E6Index K w
  have hi (i : Fin 6) (him : i∈orbitWord a) :
      (MulAut.conj W) (canonicalRoot rawData K true i 1)∈Positive K :=
    positive_negative_root_word A hd hs hp ho K w i 1 (hall i him)
  change (MulAut.conj W) (orbitParameter K true a 1)∈Positive K
  fin_cases a
  · change (MulAut.conj W) (canonicalRoot rawData K true 0 1*
      canonicalRoot rawData K true 5 1)∈Positive K
    rw [map_mul]
    exact (Positive K).mul_mem (hi 0 (by decide)) (hi 5 (by decide))
  · change (MulAut.conj W) (canonicalRoot rawData K true 2 1*
      canonicalRoot rawData K true 4 1)∈Positive K
    rw [map_mul]
    exact (Positive K).mul_mem (hi 2 (by decide)) (hi 4 (by decide))
  · exact hi 3 (by decide)
  · exact hi 1 (by decide)

theorem orbitParameter_neg (K : Type) [Field K] (neg : Bool) (a : Fin 4) (t : K) :
    orbitParameter K neg a (-t)=(orbitParameter K neg a t)⁻¹ := by
  fin_cases a
  · change canonicalRoot rawData K neg 0 (-t)*canonicalRoot rawData K neg 5 (-t)=
      (canonicalRoot rawData K neg 0 t*canonicalRoot rawData K neg 5 t)⁻¹
    rw [←canonicalRoot_inverse,←canonicalRoot_inverse,mul_inv_rev]
    exact (orthogonal_signed_roots A hs hp E6Base E6Index K 0 5
      (by rw [E6_cartan];decide) neg neg t t).inv_inv.eq
  · change canonicalRoot rawData K neg 2 (-t)*canonicalRoot rawData K neg 4 (-t)=
      (canonicalRoot rawData K neg 2 t*canonicalRoot rawData K neg 4 t)⁻¹
    rw [←canonicalRoot_inverse,←canonicalRoot_inverse,mul_inv_rev]
    exact (orthogonal_signed_roots A hs hp E6Base E6Index K 2 4
      (by rw [E6_cartan];decide) neg neg t t).inv_inv.eq
  · exact (canonicalRoot_inverse rawData K neg 3 t).symm
  · exact (canonicalRoot_inverse rawData K neg 1 t).symm

theorem exists_negative_orbit_mem (K : Type) [Field K] (sigma : K≃+*K)
    (H : Subgroup ((Matrix GeckIndex GeckIndex K)ˣ))
    (hU : signedFixed K sigma false≤H) (r : List (Fin 4))
    (hWmem : wordUnit A hs hp E6Base E6Index K (expandRelative r)∈H)
    (hne : linearAction (expandRelative r)≠1) :
    ∃a : Fin 4,orbitParameter K true a 1∈H := by
  let w := expandRelative r
  let W := wordUnit A hs hp E6Base E6Index K w
  obtain ⟨a,hall⟩ := exists_negative_orbit (inverseWord w) (inverse_action_ne_one w hne)
    (relative_inverse_commutes r)
  have hWi : wordUnit A hs hp E6Base E6Index K (inverseWord w)=W⁻¹ :=
    wordUnit_inverseWord A hs hp E6Base E6Index K w
  let x := W⁻¹*orbitParameter K true a 1*W
  have hxpos : x∈Positive K := by
    have hh := negative_conjugate_orbit_positive K (inverseWord w) a hall
    rw [hWi,inv_inv] at hh
    exact hh
  have hWfix : unitTwist K sigma W=W := by
    change unitTwist K sigma (wordUnit A hs hp E6Base E6Index K (expandRelative r))=
      wordUnit A hs hp E6Base E6Index K (expandRelative r)
    rw [word_eq_canonicalWord]
    exact relative_word_fixed K sigma r
  have hxfix : unitTwist K sigma x=x := by
    change unitTwist K sigma (W⁻¹*orbitParameter K true a 1*W)=_
    rw [map_mul,map_mul,map_inv,hWfix,orbitParameter_fixed K sigma true a 1 (map_one sigma)]
  have hxH : x∈H := hU ⟨hxpos,hxfix⟩
  have hh : W*x*W⁻¹∈H := H.mul_mem (H.mul_mem hWmem hxH) (H.inv_mem hWmem)
  have he : W*x*W⁻¹=orbitParameter K true a 1 := by dsimp only [x];group
  exact ⟨a,he ▸ hh⟩

theorem exists_simple_weyl_mem (K : Type) [Field K] (sigma : K≃+*K)
    (H : Subgroup ((Matrix GeckIndex GeckIndex K)ˣ))
    (hU : signedFixed K sigma false≤H) (r : List (Fin 4))
    (hWmem : wordUnit A hs hp E6Base E6Index K (expandRelative r)∈H)
    (hne : linearAction (expandRelative r)≠1) :
    ∃a : Fin 4,canonicalWord rawData K (orbitWord a)∈H := by
  obtain ⟨a,ha⟩ := exists_negative_orbit_mem K sigma H hU r hWmem hne
  have hpH := hU (orbitParameter_one_mem_signedFixed K sigma a)
  have hnH : orbitParameter K true a (-1)∈H := by
    rw [orbitParameter_neg]
    exact H.inv_mem ha
  refine ⟨a,?_⟩
  rw [orbit_word_parameter]
  exact H.mul_mem (H.mul_mem hpH hnH) hpH

end SymmetricSubgroupAsymptotics.CFSGE6GeckOvergroupWeylExtraction
