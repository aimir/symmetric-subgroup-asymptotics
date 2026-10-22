import SymmetricSubgroupAsymptotics.CFSGGradedDiagonalTransport
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWordLatticeSupport
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFunctionalSupport
import SymmetricSubgroupAsymptotics.CFSGWeightedDiagonalConjugation

/-! Literal diagonal characters of the original Geck lattice. Their root
scaling and Weyl-word transport are exact in every characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckCharacterDiagonal
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoGeckWordLatticeSupport CFSGDiagonalMatrixUnits
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

def characterDiagonal (K : Type) [Field K] (f : (n→ℤ)→ₗ[ℤ]ℤ) (t : Kˣ) :
    (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ :=
  diagonalHom _ K (fun j=>t^(f (latticeWeight A hs hp b j)))

theorem character_mul_positive (K : Type) [Field K] (f : (n→ℤ)→ₗ[ℤ]ℤ)
    (t : Kˣ) (i : Fin r) (a : K) :
    characterDiagonal A hs hp b K f t*canonicalRoot (realizationData A hs hp b s) K false i a=
      canonicalRoot (realizationData A hs hp b s) K false i
        (a*(t:K)^(f (s i:Roots A).val))*characterDiagonal A hs hp b K f t := by
  apply Units.ext
  simp only [Units.val_mul,characterDiagonal,diagonalHom_val,canonicalRoot_val,
    Units.val_zpow_eq_zpow_val]
  exact CFSGWeightedDiagonalConjugation.quadratic_mul_scaled
    (fun j=>f (latticeWeight A hs hp b j)) t (f (s i:Roots A).val)
    (fieldRoot (realizationData A hs hp b s) K false i)
    (fieldSecond (realizationData A hs hp b s) K false i)
    (by
      intro u v huv
      apply field_E_lattice_support A hs hp b s K i u v
      intro he
      apply huv
      simpa only [map_add] using congrArg f he)
    (by
      intro u v huv
      apply field_second_lattice_support A hs hp b s K i u v
      intro he
      apply huv
      simpa only [map_add,map_nsmul,two_nsmul,two_mul] using congrArg f he) a

theorem character_conjugate_positive (K : Type) [Field K] (f : (n→ℤ)→ₗ[ℤ]ℤ)
    (t : Kˣ) (i : Fin r) (a : K) :
    characterDiagonal A hs hp b K f t*canonicalRoot (realizationData A hs hp b s) K false i a*
      (characterDiagonal A hs hp b K f t)⁻¹=
      canonicalRoot (realizationData A hs hp b s) K false i (a*(t:K)^(f (s i:Roots A).val)) := by
  rw [character_mul_positive,mul_assoc,mul_inv_cancel,mul_one]

theorem word_conjugate_character (K : Type) [Field K] (f : (n→ℤ)→ₗ[ℤ]ℤ)
    (t : Kˣ) (w : List (Fin r)) :
    wordUnit A hs hp b s K w*characterDiagonal A hs hp b K f t*(wordUnit A hs hp b s K w)⁻¹=
      characterDiagonal A hs hp b K
        (f.comp (wordLinear A hs hp b s w).symm.toLinearMap) t := by
  exact CFSGGradedDiagonalTransport.unit_conjugate_diagonal
    (latticeWeight A hs hp b) (wordLinear A hs hp b s w).toEquiv
    (fun x=>t^(f x)) (wordUnit A hs hp b s K w)
    (word_lattice_support A hs hp b s K w)

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckCharacterDiagonal
