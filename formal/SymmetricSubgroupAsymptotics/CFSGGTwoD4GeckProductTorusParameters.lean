import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckRelativeProductTorus

/-! The actual relative product torus scales the two signed simple
charts by the literal G2 Cartan power map and its inverse on negatives.
All three short-orbit factors retain the SAME parameter. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckProductTorusParameters
open CFSGGTwoD4GeckProductTorus CFSGGTwoD4GeckRelativeProductTorus
open CFSGGTwoD4GeckScalarTorus CFSGGTwoD4GeckScalarTuple CFSGGTwoD4GeckSimpleParameters
open CFSGTrialityGeckFixedRootWords CFSGTrialityGeckDiagramCovariance
open CFSGIntegerMatrixPowerHom CFSGSerreQuadraticMatrix
variable (K : Type) [Field K] [Finite K]

/-- Unit-valued signed scalar, with false/true labelling short/long. -/
def parameterScalar (x : Fin 2→Kˣ) (neg a : Bool) : Kˣ :=
  if neg then (powerHom (G:=Kˣ) relativeCartan x (if a then 1 else 0))⁻¹
    else powerHom (G:=Kˣ) relativeCartan x (if a then 1 else 0)

omit [Finite K] in
theorem parameterScalar_val (x : Fin 2→Kˣ) (neg a : Bool) :
    (parameterScalar K x neg a : K)=if neg then
      (powerHom (G:=Kˣ) relativeCartan x (if a then 1 else 0) : K)⁻¹
      else (powerHom (G:=Kˣ) relativeCartan x (if a then 1 else 0) : K) := by
  cases neg
  · rfl
  · exact Units.val_inv_eq_inv_val _

private theorem raw_short_action (x : Fin 2→Kˣ) (neg : Bool) (t : K) :
    rawProductTorus K (scalarTupleHom x)*shortOrbit K (RingEquiv.refl K) neg t*
      (rawProductTorus K (scalarTupleHom x))⁻¹=
        shortOrbit K (RingEquiv.refl K) neg (t*(parameterScalar K x neg false : K)) := by
  have h0 : powerHom (G:=Kˣ) (CartanMatrix.D 4) (scalarTupleHom x) 0=powerHom (G:=Kˣ) relativeCartan x 0 :=
    congrFun (powerHom_scalarTuple x) 0
  have h2 : powerHom (G:=Kˣ) (CartanMatrix.D 4) (scalarTupleHom x) 2=powerHom (G:=Kˣ) relativeCartan x 0 :=
    congrFun (powerHom_scalarTuple x) 2
  have h3 : powerHom (G:=Kˣ) (CartanMatrix.D 4) (scalarTupleHom x) 3=powerHom (G:=Kˣ) relativeCartan x 0 :=
    congrFun (powerHom_scalarTuple x) 3
  have he0 := rawProductTorus_signed_action K (scalarTupleHom x) neg 0 t
  have he2 := rawProductTorus_signed_action K (scalarTupleHom x) neg 2 t
  have he3 := rawProductTorus_signed_action K (scalarTupleHom x) neg 3 t
  rw [h0] at he0
  rw [h2] at he2
  rw [h3] at he3
  let T := rawProductTorus K (scalarTupleHom x)
  change T*(canonicalRoot rawData K neg 0 t*canonicalRoot rawData K neg 2 t*
    canonicalRoot rawData K neg 3 t)*T⁻¹=_
  calc
    _=(T*canonicalRoot rawData K neg 0 t*T⁻¹)*
        (T*canonicalRoot rawData K neg 2 t*T⁻¹)*
        (T*canonicalRoot rawData K neg 3 t*T⁻¹) := by group
    _=_ := by
      rw [he0,he2,he3]
      rw [parameterScalar_val]
      simp only [Bool.false_eq_true,if_false,shortOrbit,RingEquiv.refl_apply]

private theorem raw_long_action (x : Fin 2→Kˣ) (neg : Bool) (t : K) :
    rawProductTorus K (scalarTupleHom x)*canonicalRoot rawData K neg 1 t*
      (rawProductTorus K (scalarTupleHom x))⁻¹=
        canonicalRoot rawData K neg 1 (t*(parameterScalar K x neg true : K)) := by
  have h1 : powerHom (G:=Kˣ) (CartanMatrix.D 4) (scalarTupleHom x) 1=powerHom (G:=Kˣ) relativeCartan x 1 :=
    congrFun (powerHom_scalarTuple x) 1
  have he := rawProductTorus_signed_action K (scalarTupleHom x) neg 1 t
  rw [h1] at he
  simpa only [parameterScalar_val] using he

theorem relativeProductTorus_simple_action (x : Fin 2→Kˣ) (neg a : Bool) (t : K) :
    relativeProductTorus K x*simpleGeneratedHom K neg a (Multiplicative.ofAdd t)*
      (relativeProductTorus K x)⁻¹=
        simpleGeneratedHom K neg a (Multiplicative.ofAdd (t*(parameterScalar K x neg a : K))) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul,Subgroup.coe_inv,relativeProductTorus_val,simpleGeneratedHom_val]
  cases a
  · exact raw_short_action K x neg t
  · exact raw_long_action K x neg t

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckProductTorusParameters
