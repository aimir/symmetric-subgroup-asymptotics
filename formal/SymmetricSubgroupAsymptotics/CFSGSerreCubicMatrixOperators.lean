import SymmetricSubgroupAsymptotics.CFSGSerreCubicMatrixData
import SymmetricSubgroupAsymptotics.CFSGIntegralCubicRootOperators
import SymmetricSubgroupAsymptotics.CFSGIntegerMatrixBaseChange

/-! Shared integral divided-power and original tensor-base-change
intertwiners for genuine cubic-root matrix realizations. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGSerreCubicMatrix
open CFSG.Models.Chevalley
variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I]

theorem integralRepresentation_operator (D : Data A I) (neg : Bool) (i : Fin n) (k : ℕ)
    (x : integralLattice A) :
    integralRepresentation D (integralOperator A neg i k x)=
      CFSGIntegralCubicRootOperators.operator ℤ (integerRoot D neg i) (D.integerSecond neg i) (D.integerThird neg i) k (integralRepresentation D x) := by
  apply CFSGSerreSquareZeroMatrix.integerCast_injective I
  rw [integralRepresentation_cast]
  change D.rational (dividedPower A neg i k x.val)=
    (Int.castRingHom ℚ).mapMatrix
      (CFSGIntegralCubicRootOperators.operator ℤ (integerRoot D neg i) (D.integerSecond neg i) (D.integerThird neg i) k (integralRepresentation D x))
  rw [CFSGSerreIntegralRepresentation.dividedPower_intertwines,rational_rootVector]
  rw [CFSGCubicRootDividedPowers.rational_operator _ _ _ (fieldRoot_square D ℚ neg i)
      (fieldRoot_mul_second D ℚ neg i) (fieldSecond_mul_root D ℚ neg i)
      (fieldRoot_mul_third D ℚ neg i) (fieldThird_mul_root D ℚ neg i),
    CFSGIntegralCubicRootOperators.map_operator]
  rw [CFSGIntegralCubicRootOperators.operator_changeScalars ℤ ℚ]
  exact congrArg (CFSGIntegralCubicRootOperators.operator ℚ (fieldRoot D ℚ neg i) (fieldSecond D ℚ neg i) (fieldThird D ℚ neg i) k)
    (integralRepresentation_cast D x).symm

def baseChange (D : Data A I) (K : Type*) [CommRing K] :
    (K ⊗[ℤ] integralLattice A)→ₗ[K]Matrix I I K :=
  (CFSGIntegerMatrixBaseChange.tensorMap K I).comp ((integralRepresentation D).baseChange K)

theorem baseChange_tmul (D : Data A I) (K : Type*) [CommRing K]
    (a : K) (x : integralLattice A) :
    baseChange D K (a ⊗ₜ[ℤ] x)=a • (Int.castRingHom K).mapMatrix (integralRepresentation D x) := by
  rw [baseChange,LinearMap.comp_apply,LinearMap.baseChange_tmul,
    CFSGIntegerMatrixBaseChange.tensorMap_tmul]
  rfl

theorem baseChange_generator (D : Data A I) (K : Type*) [CommRing K]
    (g : CartanMatrix.Generators (Fin n)) :
    baseChange D K (1 ⊗ₜ[ℤ] CFSGSerreDiagram.latticeGenerator A g)=
      (Int.castRingHom K).mapMatrix (D.integerGenerator g) := by
  rw [baseChange_tmul,integralRepresentation_generator,one_smul]

theorem baseChange_operator (D : Data A I) (K : Type*) [CommRing K]
    (neg : Bool) (i : Fin n) (k : ℕ) (x : K ⊗[ℤ] integralLattice A) :
    baseChange D K ((integralOperator A neg i k).baseChange K x)=
      CFSGIntegralCubicRootOperators.operator K (fieldRoot D K neg i) (fieldSecond D K neg i) (fieldThird D K neg i) k (baseChange D K x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x =>
    rw [LinearMap.baseChange_tmul,baseChange_tmul,integralRepresentation_operator,baseChange_tmul]
    change a • (Int.castRingHom K).mapMatrix
      (CFSGIntegralCubicRootOperators.operator ℤ (integerRoot D neg i) (D.integerSecond neg i) (D.integerThird neg i) k (integralRepresentation D x))=
      CFSGIntegralCubicRootOperators.operator K (fieldRoot D K neg i) (fieldSecond D K neg i) (fieldThird D K neg i) k
        (a • (Int.castRingHom K).mapMatrix (integralRepresentation D x))
    rw [CFSGIntegralCubicRootOperators.map_operator,
      CFSGIntegralCubicRootOperators.operator_changeScalars ℤ K,map_smul]
    rfl
  | add x y hx hy => simp only [map_add,hx,hy]

end SymmetricSubgroupAsymptotics.CFSGSerreCubicMatrix
