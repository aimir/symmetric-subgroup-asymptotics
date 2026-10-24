import SymmetricSubgroupAsymptotics.CFSGE6GeckProductTorusWeylAction
import SymmetricSubgroupAsymptotics.CFSGFFourE6ScalarTuple
import Mathlib.Algebra.BigOperators.Fin

/-! A bounded integral cocharacter certificate for the outer relative
reflection. It acts on the literal folded six-tuple, over any commutative
group; no group normalizer or Weyl recognition is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckOuterTorusExponentCertificate
open CFSGE6GeckProductTorusWeylAction CFSGIntegerMatrixPowerHom
open CFSGRectangularMatrixPowerHom CFSGFFourE6ScalarTuple

def outerExponents : Matrix (Fin 4) (Fin 4) ℤ :=
  !![-1,1,0,0;0,1,0,0;0,0,1,0;0,0,1,-1]

theorem outer_embedding :
    wordReflectionExponents [0,5,1]*embedding=embedding*outerExponents := by decide +kernel

theorem outer_folded_tuple {G : Type*} [CommGroup G] (x : Fin 4 → G) :
    powerHom (wordReflectionExponents [0,5,1]) (scalarTupleHom x)=
      scalarTupleHom (powerHom outerExponents x) := by
  change matrixPowerHom (wordReflectionExponents [0,5,1]) (scalarTupleHom x)=
    scalarTupleHom (matrixPowerHom outerExponents x)
  calc
    _=matrixPowerHom (wordReflectionExponents [0,5,1]) (matrixPowerHom embedding x) :=
      congrArg (matrixPowerHom (wordReflectionExponents [0,5,1])) (embedding_value x).symm
    _=matrixPowerHom (wordReflectionExponents [0,5,1]*embedding) x := (matrixPowerHom_mul _ _ x).symm
    _=matrixPowerHom (embedding*outerExponents) x := congrArg (fun M=>matrixPowerHom M x) outer_embedding
    _=matrixPowerHom embedding (matrixPowerHom outerExponents x) := matrixPowerHom_mul _ _ x
    _=_ := embedding_value _

theorem outer_exponents_value {G : Type*} [CommGroup G] (x : Fin 4 → G) :
    powerHom outerExponents x=![x 1*(x 0)⁻¹,x 1,x 2,x 2*(x 3)⁻¹] := by
  funext i
  rw [powerHom_apply,Fin.prod_univ_four]
  fin_cases i
  · change x 0^(-1:ℤ)*x 1^(1:ℤ)*x 2^(0:ℤ)*x 3^(0:ℤ)=x 1*(x 0)⁻¹
    simp [mul_comm]
  · change x 0^(0:ℤ)*x 1^(1:ℤ)*x 2^(0:ℤ)*x 3^(0:ℤ)=x 1
    simp
  · change x 0^(0:ℤ)*x 1^(0:ℤ)*x 2^(1:ℤ)*x 3^(0:ℤ)=x 2
    simp
  · change x 0^(0:ℤ)*x 1^(0:ℤ)*x 2^(1:ℤ)*x 3^(-1:ℤ)=x 2*(x 3)⁻¹
    simp

end SymmetricSubgroupAsymptotics.CFSGE6GeckOuterTorusExponentCertificate
