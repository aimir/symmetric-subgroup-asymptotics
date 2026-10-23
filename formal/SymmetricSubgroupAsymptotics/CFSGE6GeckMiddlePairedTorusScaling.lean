import SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleTorusScaling
import SymmetricSubgroupAsymptotics.CFSGE6GeckPairedParameterizedWeyl

/-! The actual paired rank-one torus scales the middle singleton-root
word by the product of its two literal field parameters. This is proved
on the same matrices, before restricting that product to a fixed field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckMiddlePairedTorusScaling
open CFSGE6GeckMiddleTorusScaling CFSGE6GeckPairedParameterizedWeyl
open CFSGE6GeckMiddleAThreeCollecting CFSGTwistedE6GeckDiagramCovariance
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoGeckParameterizedTorus CFSGNormTwoGeckParameterizedWeyl

theorem middleLong_paired_torus_scale (K : Type) [Field K] (sigma : RingAut K)
    (t : Kˣ) (a : K) :
    pairedParameterTorus K sigma 1 t*highestMiddle K a*(pairedParameterTorus K sigma 1 t)⁻¹=
      highestMiddle K (a*((t : K)*sigma (t : K))) := by
  rw [pairedParameterTorus_eq]
  let H := parameterTorus CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K 2 t
  let J := parameterTorus CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K 4
    ((Units.map sigma.toMonoidHom) t)
  change (H*J)*highestMiddle K a*(H*J)⁻¹=_
  have hJ : J*highestMiddle K a*J⁻¹=highestMiddle K (a*sigma (t : K)) :=
    middleLong_torus_outer K 1 ((Units.map sigma.toMonoidHom) t) a
  have hH : H*highestMiddle K (a*sigma (t : K))*H⁻¹=
      highestMiddle K ((a*sigma (t : K))*(t : K)) :=
    middleLong_torus_outer K 0 t (a*sigma (t : K))
  calc
    _=H*(J*highestMiddle K a*J⁻¹)*H⁻¹ := by group
    _=highestMiddle K ((a*sigma (t : K))*(t : K)) := by rw [hJ,hH]
    _=_ := by congr 1; ring

end SymmetricSubgroupAsymptotics.CFSGE6GeckMiddlePairedTorusScaling
