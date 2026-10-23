import SymmetricSubgroupAsymptotics.CFSGFFourE6ProductTorus
import SymmetricSubgroupAsymptotics.CFSGE6GeckProductTorusSigned
import SymmetricSubgroupAsymptotics.CFSGFieldScaledRootHom
import Mathlib.Tactic.Group

/-! The actual native product torus realizes the literal F4 relative
Cartan map on every signed original simple chart, and preserves each
such full chart range. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6ProductTorusAction
open CFSGFFourE6ProductTorus CFSGFFourRelativeScalarIndex
open CFSGE6GeckProductTorusSigned CFSGE6GeckProductTorus CFSGIntegerMatrixPowerHom
open CFSGFFourE6SimpleGeneratedParameters CFSGFFourE6OriginalSimpleParameters
open CFSGFFourE6GeneratedOriginalProjection CFSGE6GeckSignedSimpleParameters
open CFSGE6GeckRelativeSimpleHom CFSGE6GeckFixedOrbitRootGroups
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6PairedFixedRoots
open CFSGTwistedE6FixedA2 CFSGSerreQuadraticMatrix CFSGFieldScaledRootHom CFSG.Models.Chevalley

private theorem paired_action (K : Type) [Field K] (x : Fin 4→Kˣ) (neg : Bool) (j : Fin 2) (a : K) :
    rawProductTorus K (torusTuple K x)*rawPairedHom K (RingEquiv.refl K) neg j (Multiplicative.ofAdd a)*
      (rawProductTorus K (torusTuple K x))⁻¹=
    rawPairedHom K (RingEquiv.refl K) neg j (Multiplicative.ofAdd
      (a*(if neg then (powerHom (G := Kˣ) relativeCartan x (pairedOrbit j) : K)⁻¹
        else (powerHom (G := Kˣ) relativeCartan x (pairedOrbit j) : K)))) := by
  have hnode : powerHom (G := Kˣ) CartanMatrix.E₆ (torusTuple K x) (pairedNode j)=
      powerHom (G := Kˣ) relativeCartan x (pairedOrbit j) := by
    rw [powerHom_torusTuple]
    fin_cases j <;> rfl
  have hpartner : powerHom (G := Kˣ) CartanMatrix.E₆ (torusTuple K x) (pairedPartner j)=
      powerHom (G := Kˣ) relativeCartan x (pairedOrbit j) := by
    rw [powerHom_torusTuple]
    fin_cases j <;> rfl
  change rawProductTorus K (torusTuple K x)*
      (canonicalRoot rawData K neg (pairedNode j) a*canonicalRoot rawData K neg (pairedPartner j) a)*
      (rawProductTorus K (torusTuple K x))⁻¹=_
  calc
    _=(rawProductTorus K (torusTuple K x)*canonicalRoot rawData K neg (pairedNode j) a*
        (rawProductTorus K (torusTuple K x))⁻¹)*
      (rawProductTorus K (torusTuple K x)*canonicalRoot rawData K neg (pairedPartner j) a*
        (rawProductTorus K (torusTuple K x))⁻¹) := by group
    _=_ := by
      rw [rawProductTorus_signed_action,rawProductTorus_signed_action,hnode,hpartner]
      rfl

private theorem singleton_action (K : Type) [Field K] (x : Fin 4→Kˣ) (neg : Bool) (j : Fin 2) (a : K) :
    rawProductTorus K (torusTuple K x)*rawSingletonHom K neg j (Multiplicative.ofAdd a)*
      (rawProductTorus K (torusTuple K x))⁻¹=
    rawSingletonHom K neg j (Multiplicative.ofAdd
      (a*(if neg then (powerHom (G := Kˣ) relativeCartan x (singletonOrbit j) : K)⁻¹
        else (powerHom (G := Kˣ) relativeCartan x (singletonOrbit j) : K)))) := by
  have hnode : powerHom (G := Kˣ) CartanMatrix.E₆ (torusTuple K x) (node j)=
      powerHom (G := Kˣ) relativeCartan x (singletonOrbit j) := by
    rw [powerHom_torusTuple]
    fin_cases j <;> rfl
  change rawProductTorus K (torusTuple K x)*canonicalRoot rawData K neg (node j) a*
    (rawProductTorus K (torusTuple K x))⁻¹=_
  rw [rawProductTorus_signed_action,hnode]
  rfl

theorem generated_product_torus_action (K : Type) [Field K] (x : Fin 4→Kˣ) (neg : Bool) (i : Fin 4) (a : K) :
    productTorusGenerated K x*simpleInGenerated K neg i (Multiplicative.ofAdd a)*
      (productTorusGenerated K x)⁻¹=
    simpleInGenerated K neg i (Multiplicative.ofAdd
      (a*(if neg then (powerHom (G := Kˣ) relativeCartan x i : K)⁻¹
        else (powerHom (G := Kˣ) relativeCartan x i : K)))) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul,Subgroup.coe_inv,productTorusGenerated_val,simpleInGenerated_val]
  fin_cases i
  · exact paired_action K x neg 0 a
  · exact paired_action K x neg 1 a
  · exact singleton_action K x neg 1 a
  · exact singleton_action K x neg 0 a

theorem original_product_torus_action (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] (x : Fin 4→Kˣ) (neg : Bool) (i : Fin 4) (a : K) :
    originalProductTorusHom K x*originalSimpleHom K neg i (Multiplicative.ofAdd a)*
      (originalProductTorusHom K x)⁻¹=
    originalSimpleHom K neg i (Multiplicative.ofAdd
      ((if neg then (powerHom (G := Kˣ) relativeCartan x i : K)⁻¹
        else (powerHom (G := Kˣ) relativeCartan x i : K))*a)) := by
  have he := congrArg (generatedToOriginal K) (generated_product_torus_action K x neg i a)
  simpa only [map_mul,map_inv,simpleInGenerated_original,mul_comm] using he

theorem original_product_torus_chart (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] (x : Fin 4→Kˣ) (neg : Bool) (i : Fin 4) :
    (originalSimpleHom K neg i).range.map (MulAut.conj (originalProductTorusHom K x)).toMonoidHom=
      (originalSimpleHom K neg i).range := by
  let c : Kˣ := if neg then (powerHom (G := Kˣ) relativeCartan x i)⁻¹ else powerHom (G := Kˣ) relativeCartan x i
  rw [MonoidHom.map_range]
  have he : (MulAut.conj (originalProductTorusHom K x)).toMonoidHom.comp (originalSimpleHom K neg i)=
      scaledHom (originalSimpleHom K neg i) (c : K) := by
    apply MonoidHom.ext
    intro a
    change originalProductTorusHom K x*originalSimpleHom K neg i a*(originalProductTorusHom K x)⁻¹=
      originalSimpleHom K neg i (Multiplicative.ofAdd ((c : K)*a.toAdd))
    cases neg
    · simpa only [c,Bool.false_eq_true,if_false,ofAdd_toAdd] using
        original_product_torus_action K x false i a.toAdd
    · simpa only [c,if_true,Units.val_inv_eq_inv_val,ofAdd_toAdd] using
        original_product_torus_action K x true i a.toAdd
  rw [he]
  exact scaledHom_range _ _ c.ne_zero

end SymmetricSubgroupAsymptotics.CFSGFFourE6ProductTorusAction
