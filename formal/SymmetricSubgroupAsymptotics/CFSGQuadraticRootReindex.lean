import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrixData
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! Covariance of integral quadratic root coefficients under an actual
basis permutation. The second coefficient is forced by E^2=d+d over
the torsion-free INTEGER matrices. Every subsequent base change is
therefore valid, including characteristics two and three. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticRootReindex
open CFSGSerreQuadraticMatrix
variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I]

theorem integer_eq_of_rational (σ : Equiv.Perm I) (M N : Matrix I I ℤ)
    (h : Matrix.reindexAlgEquiv ℚ ℚ σ ((Int.castRingHom ℚ).mapMatrix M)=
      (Int.castRingHom ℚ).mapMatrix N) : Matrix.reindexAlgEquiv ℤ ℤ σ M=N := by
  apply CFSGSerreSquareZeroMatrix.integerCast_injective I
  exact h

theorem integerSecond_reindex (D : Data A I) (σ : Equiv.Perm I) (p : Equiv.Perm (Fin n))
    (hroot : ∀ neg i,Matrix.reindexAlgEquiv ℤ ℤ σ (integerRoot D neg i)=integerRoot D neg (p i))
    (neg : Bool) (i : Fin n) :
    Matrix.reindexAlgEquiv ℤ ℤ σ (D.integerSecond neg i)=D.integerSecond neg (p i) := by
  let τ:=Matrix.reindexAlgEquiv ℤ ℤ σ
  have hh:=congrArg τ (D.root_square neg i)
  change τ (integerRoot D neg i*integerRoot D neg i)=
    τ (D.integerSecond neg i+D.integerSecond neg i) at hh
  simp only [τ,map_mul,map_add,hroot] at hh
  have ht : τ (D.integerSecond neg i)+τ (D.integerSecond neg i)=
      D.integerSecond neg (p i)+D.integerSecond neg (p i) :=
    hh.symm.trans (D.root_square neg (p i))
  ext x y
  have he:=congrArg (fun M : Matrix I I ℤ=>M x y) ht
  change τ (D.integerSecond neg i) x y+τ (D.integerSecond neg i) x y=
    D.integerSecond neg (p i) x y+D.integerSecond neg (p i) x y at he
  change τ (D.integerSecond neg i) x y=D.integerSecond neg (p i) x y
  omega

theorem fieldRoot_reindex (D : Data A I) (σ : Equiv.Perm I) (p : Equiv.Perm (Fin n))
    (hroot : ∀ neg i,Matrix.reindexAlgEquiv ℤ ℤ σ (integerRoot D neg i)=integerRoot D neg (p i))
    (K : Type*) [CommRing K] (neg : Bool) (i : Fin n) :
    Matrix.reindexAlgEquiv K K σ (fieldRoot D K neg i)=fieldRoot D K neg (p i) := by
  exact congrArg (Int.castRingHom K).mapMatrix (hroot neg i)

theorem fieldSecond_reindex (D : Data A I) (σ : Equiv.Perm I) (p : Equiv.Perm (Fin n))
    (hroot : ∀ neg i,Matrix.reindexAlgEquiv ℤ ℤ σ (integerRoot D neg i)=integerRoot D neg (p i))
    (K : Type*) [CommRing K] (neg : Bool) (i : Fin n) :
    Matrix.reindexAlgEquiv K K σ (fieldSecond D K neg i)=fieldSecond D K neg (p i) := by
  exact congrArg (Int.castRingHom K).mapMatrix (integerSecond_reindex D σ p hroot neg i)

end SymmetricSubgroupAsymptotics.CFSGQuadraticRootReindex
