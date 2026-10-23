import SymmetricSubgroupAsymptotics.CFSGFFourE6RelativeTorus
import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalMiddleFactors
import SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleTorusScaling
import SymmetricSubgroupAsymptotics.CFSGE6GeckMiddlePairedTorusScaling

/-! Actual native F4 torus scaling on the two middle factors. The paired
torus gives a square, while the singleton torus gives coefficient one;
no square-root extraction or characteristic restriction is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalMiddleTorus
open CFSGFFourE6RelativeTorus CFSGFFourE6OriginalMiddleFactors
open CFSGFFourE6GeneratedOriginalProjection CFSGE6GeckMiddleTorusScaling
open CFSGE6GeckMiddlePairedTorusScaling CFSGE6GeckFixedOrbitRootGroups
open CFSGE6GeckMiddleFactorInjective CFSG.Models.Chevalley

theorem torus_middleShort (K : Type) [Field K] (t : Kˣ) (a : K) :
    torusInGenerated K 2 t*middleShortInGenerated K a*(torusInGenerated K 2 t)⁻¹=
      middleShortInGenerated K (a*(t : K)) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul,Subgroup.coe_inv,middleShortInGenerated_val]
  have ht := torusInGenerated_singleton_val K 1 t
  change (torusInGenerated K 2 t).val=_ at ht
  rw [ht]
  exact middleShort_torus_scale K (RingEquiv.refl K) t rfl a

theorem torus_middleLong (K : Type) [Field K] (t : Kˣ) (a : K) :
    torusInGenerated K 1 t*middleLongInGenerated K a*(torusInGenerated K 1 t)⁻¹=
      middleLongInGenerated K (a*((t : K)*(t : K))) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul,Subgroup.coe_inv,middleLongInGenerated_val]
  have ht := torusInGenerated_paired_val K 1 t
  change (torusInGenerated K 1 t).val=_ at ht
  rw [ht]
  exact middleLong_paired_torus_scale K (RingEquiv.refl K) t a

theorem original_torus_middleShort (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] (t : Kˣ) (a : K) :
    generatedToOriginal K (torusInGenerated K 2 t)*middleShortOriginalHom K (Multiplicative.ofAdd a)*
      (generatedToOriginal K (torusInGenerated K 2 t))⁻¹=
      middleShortOriginalHom K (Multiplicative.ofAdd (a*(t : K))) := by
  simpa only [map_mul,map_inv,middleShortInGenerated_original] using
    congrArg (generatedToOriginal K) (torus_middleShort K t a)

theorem original_torus_middleLong (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] (t : Kˣ) (a : K) :
    generatedToOriginal K (torusInGenerated K 1 t)*middleLongOriginalHom K (Multiplicative.ofAdd a)*
      (generatedToOriginal K (torusInGenerated K 1 t))⁻¹=
      middleLongOriginalHom K (Multiplicative.ofAdd (a*((t : K)*(t : K)))) := by
  simpa only [map_mul,map_inv,middleLongInGenerated_original] using
    congrArg (generatedToOriginal K) (torus_middleLong K t a)

end SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalMiddleTorus
