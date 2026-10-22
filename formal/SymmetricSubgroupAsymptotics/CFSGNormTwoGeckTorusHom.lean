import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckDiagonalTorus
import SymmetricSubgroupAsymptotics.CFSGDiagonalMatrixUnits

/-! The literal rank-one torus parameter is a homomorphism of units.
The proof uses its checked diagonal columns, in every field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckTorusHom
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckParameterizedTorus CFSGNormTwoGeckDiagonalTorus
open CFSGDiagonalMatrixUnits
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

def torusWeightHom (K : Type*) [Field K] (i : Fin r) :
    Kˣ→*(b.support⊕Roots A→Kˣ) where
  toFun t k := t^(weight A hs hp b s i k)
  map_one' := by funext k; simp only [one_zpow,Pi.one_apply]
  map_mul' := by intro t u; funext k; exact mul_zpow t u _

def parameterTorusHom (K : Type*) [Field K] (i : Fin r) :
    Kˣ→*(Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ :=
  (diagonalHom (b.support⊕Roots A) K).comp (torusWeightHom A hs hp b s K i)

theorem parameterTorusHom_apply (K : Type*) [Field K] (i : Fin r) (t : Kˣ) :
    parameterTorusHom A hs hp b s K i t=parameterTorus A hs hp b s K i t := by
  apply Units.ext
  change (diagonalHom (b.support⊕Roots A) K
    (fun k=>t^(weight A hs hp b s i k)) : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)=_
  rw [diagonalHom_val,torus_diagonal]
  congr 1
  funext k
  exact Units.val_zpow_eq_zpow_val t _

theorem parameterTorus_inverse (K : Type*) [Field K] (i : Fin r) (t : Kˣ) :
    (parameterTorus A hs hp b s K i t)⁻¹=parameterTorus A hs hp b s K i t⁻¹ := by
  rw [←parameterTorusHom_apply,←parameterTorusHom_apply,map_inv]

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckTorusHom
