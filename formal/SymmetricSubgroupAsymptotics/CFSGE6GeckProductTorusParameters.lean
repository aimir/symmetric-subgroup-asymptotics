import SymmetricSubgroupAsymptotics.CFSGE6GeckProductTorus
import Mathlib.Tactic.Group

/-! The literal Cartan scaling of the product torus descends to the
paired K-parameters and singleton fixed-subfield parameters. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckProductTorusParameters
open CFSGE6GeckProductTorus CFSGE6GeckRelativeScalarCoordinates
open CFSGE6GeckRelativeScalarTuples CFSGE6GeckFixedSimpleParameters
open CFSGE6GeckSignedSimpleParameters CFSGTwistedE6GeckDiagramCovariance
open CFSGTwistedE6PairedFixedRoots CFSGTwistedE6FixedA2 CFSGSerreQuadraticMatrix

variable (K : Type) [Field K] (sigma : RingAut K)

def pairedScaleHom : relativeScalars K sigma→*(Fin 2→Kˣ) where
  toFun x j := x.val (pairedNode j)
  map_one' := rfl
  map_mul' _ _ := rfl

def singletonScaleHom : relativeScalars K sigma→*(Fin 2→(fixedCoefficient K sigma)ˣ) where
  toFun x j := fixedScalar K sigma x (node j) (by fin_cases j <;> decide)
  map_one' := by funext j; exact Units.ext (Subtype.ext rfl)
  map_mul' _ _ := by funext j; exact Units.ext (Subtype.ext rfl)

theorem product_torus_paired_action (x : relativeScalars K sigma) (j : Fin 2) (a : K) :
    rawProductTorus K x.val*rawPairedHom K sigma false j (Multiplicative.ofAdd a)*
        (rawProductTorus K x.val)⁻¹=
      rawPairedHom K sigma false j
        (Multiplicative.ofAdd (a*((relativePowerHom K sigma x).val (pairedNode j) : K))) := by
  let y := relativePowerHom K sigma x
  have hy : sigma (y.val (pairedNode j) : K)=(y.val (pairedPartner j) : K) := by
    have he := y.property (pairedNode j)
    exact congrArg Units.val he
  change rawProductTorus K x.val*
      (canonicalRoot rawData K false (pairedNode j) a*
        canonicalRoot rawData K false (pairedPartner j) (sigma a))*
        (rawProductTorus K x.val)⁻¹=
      canonicalRoot rawData K false (pairedNode j) (a*(y.val (pairedNode j) : K))*
        canonicalRoot rawData K false (pairedPartner j) (sigma (a*(y.val (pairedNode j) : K)))
  calc
    _=(rawProductTorus K x.val*canonicalRoot rawData K false (pairedNode j) a*
        (rawProductTorus K x.val)⁻¹)*
      (rawProductTorus K x.val*canonicalRoot rawData K false (pairedPartner j) (sigma a)*
        (rawProductTorus K x.val)⁻¹) := by group
    _=_ := by
      rw [rawProductTorus_simple_action,rawProductTorus_simple_action,map_mul,hy]
      rfl

theorem product_torus_singleton_action (x : relativeScalars K sigma) (j : Fin 2)
    (a : fixedCoefficient K sigma) :
    rawProductTorus K x.val*rawSingletonHom K false j (Multiplicative.ofAdd (a : K))*
        (rawProductTorus K x.val)⁻¹=
      rawSingletonHom K false j (Multiplicative.ofAdd
        (((a*(fixedScalar K sigma (relativePowerHom K sigma x) (node j)
          (by fin_cases j <;> decide) : fixedCoefficient K sigma)) : K))) := by
  change rawProductTorus K x.val*canonicalRoot rawData K false (node j) (a : K)*
    (rawProductTorus K x.val)⁻¹=canonicalRoot rawData K false (node j) _
  rw [rawProductTorus_simple_action]
  rfl

end SymmetricSubgroupAsymptotics.CFSGE6GeckProductTorusParameters
