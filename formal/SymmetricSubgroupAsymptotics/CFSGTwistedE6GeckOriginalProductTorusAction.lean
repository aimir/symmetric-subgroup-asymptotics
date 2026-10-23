import SymmetricSubgroupAsymptotics.CFSGE6GeckProductTorusParameters
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeProductTorus

/-! Actual inner words realize the restricted E6 Cartan map on every
positive original paired and singleton simple parameter. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalProductTorusAction
open CFSGE6GeckProductTorusParameters CFSGE6GeckRelativeScalarTuples
open CFSGTwistedE6GeckRelativeProductTorus CFSGTwistedE6GeckRelativeTorus
open CFSGTwistedE6GeckOriginalProjection CFSGTwistedE6GeckOriginalSimpleParameters
open CFSGE6GeckSignedSimpleParameters CFSGTwistedE6GeckOriginalSingletonA2
open CFSGSerreOrdinaryTwists

theorem original_product_torus_paired (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)]
    (x : relativeScalars (q.Extension 2) (definingFieldAutomorphism q 2)) (j : Fin 2) (a : q.Extension 2) :
    originalProductTorus q x*pairedOriginalHom q false j (Multiplicative.ofAdd a)*
        (originalProductTorus q x)⁻¹=
      pairedOriginalHom q false j (Multiplicative.ofAdd
        ((pairedScaleHom _ _ (relativePowerHom _ _ x) j : q.Extension 2)*a)) := by
  have he : relativeProductTorus q x*pairedSignedInGenerated q false j (Multiplicative.ofAdd a)*
      (relativeProductTorus q x)⁻¹=
    pairedSignedInGenerated q false j (Multiplicative.ofAdd
      (a*(pairedScaleHom _ _ (relativePowerHom _ _ x) j : q.Extension 2))) := by
    apply Subtype.ext
    change (relativeProductTorus q x).val*rawPairedHom _ _ false j (Multiplicative.ofAdd a)*
      (relativeProductTorus q x).val⁻¹=rawPairedHom _ _ false j _
    rw [relativeProductTorus_val]
    exact product_torus_paired_action _ _ x j a
  have hp := congrArg (generatedToOriginal q) he
  rw [map_mul,map_mul,map_inv] at hp
  change originalProductTorus q x*pairedOriginalHom q false j (Multiplicative.ofAdd a)*
    (originalProductTorus q x)⁻¹=pairedOriginalHom q false j
      (Multiplicative.ofAdd (a*(pairedScaleHom _ _ (relativePowerHom _ _ x) j : q.Extension 2))) at hp
  simpa only [mul_comm] using hp

theorem original_product_torus_singleton (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)]
    (x : relativeScalars (q.Extension 2) (definingFieldAutomorphism q 2)) (j : Fin 2) (a : Coefficient q) :
    originalProductTorus q x*singletonOriginalHom q false j (Multiplicative.ofAdd a)*
        (originalProductTorus q x)⁻¹=
      singletonOriginalHom q false j (Multiplicative.ofAdd
        ((singletonScaleHom _ _ (relativePowerHom _ _ x) j : Coefficient q)*a)) := by
  have he : relativeProductTorus q x*singletonSignedInGenerated q false j (Multiplicative.ofAdd a)*
      (relativeProductTorus q x)⁻¹=
    singletonSignedInGenerated q false j (Multiplicative.ofAdd
      (a*(singletonScaleHom _ _ (relativePowerHom _ _ x) j : Coefficient q))) := by
    apply Subtype.ext
    change (relativeProductTorus q x).val*rawSingletonHom _ false j (Multiplicative.ofAdd (a : q.Extension 2))*
      (relativeProductTorus q x).val⁻¹=rawSingletonHom _ false j _
    rw [relativeProductTorus_val]
    exact product_torus_singleton_action _ _ x j a
  have hp := congrArg (generatedToOriginal q) he
  rw [map_mul,map_mul,map_inv] at hp
  change originalProductTorus q x*singletonOriginalHom q false j (Multiplicative.ofAdd a)*
    (originalProductTorus q x)⁻¹=singletonOriginalHom q false j
      (Multiplicative.ofAdd (a*(singletonScaleHom _ _ (relativePowerHom _ _ x) j : Coefficient q))) at hp
  simpa only [mul_comm] using hp

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalProductTorusAction
