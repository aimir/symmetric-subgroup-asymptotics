import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckRelativeProductTorus
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleSourceNormalizer
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleCentralExtensionData

/-! The literal middle-node torus belongs to the actual source normalizer
and acts with weight one on its highest-root scalar centre. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleScalarTorus
open CFSGTrialityD4NormTwo CFSGTrialityD4PositiveRootOrbits
open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckMatrixTwist
open CFSGTrialityGeckRelativeRootGenerated CFSGTrialityGeckMiddleRadicalQuotient
open CFSGGTwoD4GeckRelativeProductTorus CFSGGTwoD4GeckMiddleSourceNormalizer
open CFSGGTwoD4GeckMiddleCentralExtensionData
open CFSGNormTwoCoordinateRootTorusConjugation CFSGNormTwoGeckParameterizedTorus
open CFSGNormTwoCoordinateSelectedRootElement CFSGIntegerMatrixPairing
open CFSGNormTwoCoordinateRootLineNormalizers CFSGNormTwoCoordinateRootElementRange
open CFSGNormTwoCoordinateRootSubgroup
local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance
variable (K : Type) [Field K] [Finite K]

private abbrev torus (a : Kˣ) : Raw K := parameterTorus A hs hp Base Index K 1 a

theorem middle_torus_normalizes (a : Kˣ) :
    torus K a ∈ Subgroup.normalizer (middleRadical K : Set (Raw K)) := by
  have hle : (middleRadical K).map (MulAut.conj (torus K a)).toMonoidHom ≤
      middleRadical K := by
    apply Subgroup.map_le_iff_le_comap.mpr
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨k,hk,hm,t,he⟩
    let R : Subgroup (Raw K) := rootSubgroup A hd hs hp ho K k
    have hR : R ≤ middleRadical K := by
      intro y hy
      obtain ⟨b,hb⟩ := (mem_rootSubgroup_iff_selected A hd hs hp ho K k y).mp hy
      rw [←hb]
      exact middle_root_mem K k hk hm b
    have hx : x ∈ R := (mem_rootSubgroup_iff_selected A hd hs hp ho K k x).mpr ⟨t,he⟩
    have hmap : R.map (MulAut.conj (torus K a)).toMonoidHom = R :=
      parameterTorus_root_line A hd hs hp ho K 1 a k
    exact hR (hmap.le ⟨x,hx,rfl⟩)
  have he : (middleRadical K).map (MulAut.conj (torus K a)).toMonoidHom =
      middleRadical K := Subgroup.eq_of_le_of_card_ge hle
    (Nat.card_congr ((MulAut.conj (torus K a)).subgroupMap (middleRadical K)).toEquiv).le
  exact Subgroup.mem_normalizer_iff_conj_image_eq.mpr
    (congrArg (fun H : Subgroup (Raw K) => (H : Set (Raw K))) he)

theorem middle_torus_mem_sourceNormalizer (a : Kˣ) :
    (relativeTorusNode K true a).val ∈ sourceNormalizer K := by
  let t := relativeTorusNode K true a
  have ht : t.val = torus K a := relativeTorusNode_long_val K a
  refine ⟨?_,t.property⟩
  apply CFSGFixedSubgroupConjugation.normalizes_inf_fixed
    (unitTwist K (RingEquiv.refl K)) (middleRadical K) t.val
    (fixedRootGenerated_le_fixed K (RingEquiv.refl K) t.property)
  rw [ht]
  exact middle_torus_normalizes K a

def scalarTorus (a : Kˣ) : sourceNormalizer K :=
  ⟨(relativeTorusNode K true a).val,middle_torus_mem_sourceNormalizer K a⟩

theorem scalarTorus_central_val (a : Kˣ) (b : K) :
    (scalarTorus K a).val*(central K (Multiplicative.ofAdd b)).val*
      (scalarTorus K a).val⁻¹ = (central K (Multiplicative.ofAdd ((a : K)*b))).val := by
  have hpair : integerPairing A (Index 1 : CFSGNormTwoRootPairing.Roots A).val
      (longRoot 2).val = 1 := by
    change integerPairing A (Pi.single 1 (1 : ℤ) : Fin 4 → ℤ) (longCoordinates 2) = 1
    decide +kernel
  have hc : torus K a*(central K (Multiplicative.ofAdd b)).val*(torus K a)⁻¹ =
      (central K (Multiplicative.ofAdd
        (b*(a : K)^(integerPairing A (Index 1 : CFSGNormTwoRootPairing.Roots A).val
          (longRoot 2).val)))).val :=
    torus_conjugate_selected_root A hd hs hp ho K 1 a (longRoot 2) b
  rw [hpair,zpow_one,mul_comm b (a : K)] at hc
  change (relativeTorusNode K true a).val*_
    *((relativeTorusNode K true a).val)⁻¹ = _
  rw [relativeTorusNode_long_val]
  exact hc

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleScalarTorus
