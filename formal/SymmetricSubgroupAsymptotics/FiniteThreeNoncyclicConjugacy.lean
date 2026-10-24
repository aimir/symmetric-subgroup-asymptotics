import SymmetricSubgroupAsymptotics.FiniteThreeNoncyclicNormalBasis
import SymmetricSubgroupAsymptotics.FiniteThreeCyclicCompanion

/-! Literal GL3 conjugators for the two noncyclic normal forms. The
actual bases come from complementary eigenspaces or a square-zero chain;
no matrix classification theorem is imported. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteThreeNoncyclicConjugacy

open Module
open scoped Matrix
variable {K : Type*} [Field K]

def diagonal (a b : K) : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal ![a, a, b]

def jordan (a : K) : Matrix (Fin 3) (Fin 3) K := !![a, 0, 0; 1, a, 0; 0, 0, a]

theorem toMatrix_diagonal {V : Type*} [AddCommGroup V] [Module K V]
    (A : Module.End K V) (c : Basis (Fin 3) K V) (a b : K)
    (h0 : A (c 0) = a • c 0) (h1 : A (c 1) = a • c 1)
    (h2 : A (c 2) = b • c 2) :
    LinearMap.toMatrix c c A = diagonal a b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearMap.toMatrix_apply, diagonal, Matrix.diagonal_apply, h0, h1, h2]

theorem toMatrix_jordan {V : Type*} [AddCommGroup V] [Module K V]
    (A : Module.End K V) (c : Basis (Fin 3) K V) (a : K)
    (h0 : A (c 0) = a • c 0 + c 1) (h1 : A (c 1) = a • c 1)
    (h2 : A (c 2) = a • c 2) :
    LinearMap.toMatrix c c A = jordan a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearMap.toMatrix_apply, jordan, h0, h1, h2]

theorem exists_conjugator (A : Matrix (Fin 3) (Fin 3) K)
    (hmin : (minpoly K A).natDegree ≤ 2) :
    (∃ (P : Matrix.GeneralLinearGroup (Fin 3) K) (a b : K),
      (↑(P⁻¹) : Matrix (Fin 3) (Fin 3) K) * A *
        (P : Matrix (Fin 3) (Fin 3) K) = diagonal a b) ∨
    (∃ (P : Matrix.GeneralLinearGroup (Fin 3) K) (a : K),
      (↑(P⁻¹) : Matrix (Fin 3) (Fin 3) K) * A *
        (P : Matrix (Fin 3) (Fin 3) K) = jordan a) := by
  have hm : (minpoly K (Matrix.toLin' A)).natDegree ≤ 2 := by
    simpa only [Matrix.minpoly_toLin'] using hmin
  rcases FiniteThreeNoncyclicNormalBasis.exists_basis (Matrix.toLin' A)
    (by simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]) hm with
    ⟨c, a, b, h0, h1, h2⟩ | ⟨c, a, h0, h1, h2⟩
  · exact Or.inl ⟨FiniteThreeCyclicCompanion.basisMatrix c, a, b,
      (FiniteThreeCyclicCompanion.basisMatrix_conjugate A c).trans
        (toMatrix_diagonal (Matrix.toLin' A) c a b h0 h1 h2)⟩
  · exact Or.inr ⟨FiniteThreeCyclicCompanion.basisMatrix c, a,
      (FiniteThreeCyclicCompanion.basisMatrix_conjugate A c).trans
        (toMatrix_jordan (Matrix.toLin' A) c a h0 h1 h2)⟩

end SymmetricSubgroupAsymptotics.FiniteThreeNoncyclicConjugacy
