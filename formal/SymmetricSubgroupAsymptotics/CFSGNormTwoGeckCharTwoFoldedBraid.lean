import SymmetricSubgroupAsymptotics.CFSGThreeNodeFoldedBraid
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckA2Braid
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylSquareTorus
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrthogonalWeyl

/-! Actual characteristic-two Geck Weyl involutions and the folded A3
four-term braid. One realization datum is retained throughout. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckCharTwoFoldedBraid
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGGeckSerreRepresentation
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckWeylSquareTorus CFSGNormTwoGeckParameterizedTorus
open CFSGNormTwoGeckA2Braid CFSGNormTwoGeckOrthogonalWeyl CFSGThreeNodeFoldedBraid
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)
local notation "D" => realizationData A hs hp b s

theorem canonicalWeyl_square_charTwo (K : Type) [Field K] [CharP K 2] (i : Fin r) :
    (canonicalWeyl D K i)^2=1 := by
  have hneg : (-1 : Kˣ)=1 := by
    apply Units.ext
    change -(1 : K)=1
    exact CharTwo.neg_eq 1
  have he := torus_neg_one_eq_square A hs hp b s K i
  rw [hneg] at he
  calc
    _=parameterTorus A hs hp b s K i 1 := he.symm
    _=1 := by simp only [parameterTorus,mul_inv_cancel]

theorem canonical_folded_a3_braid (K : Type) [Field K] [CharP K 2] (i j k : Fin r)
    (hij : integerPairing A (s i : Roots A).val (s j : Roots A).val= -1)
    (hkj : integerPairing A (s k : Roots A).val (s j : Roots A).val= -1)
    (hik : cartan b s i k=0) :
    (canonicalWeyl D K i*canonicalWeyl D K k)*canonicalWeyl D K j*
      (canonicalWeyl D K i*canonicalWeyl D K k)*canonicalWeyl D K j=
    canonicalWeyl D K j*(canonicalWeyl D K i*canonicalWeyl D K k)*
      canonicalWeyl D K j*(canonicalWeyl D K i*canonicalWeyl D K k) := by
  exact folded_braid _ _ _ (orthogonal_weyls A hs hp b s K i k hik)
    (braid_of_involutions_cube _ _
      (canonicalWeyl_square_charTwo A hs hp b s K i)
      (canonicalWeyl_square_charTwo A hs hp b s K j)
      (canonical_weyl_product_cube A hs hp b s K i j hij))
    (braid_of_involutions_cube _ _
      (canonicalWeyl_square_charTwo A hs hp b s K k)
      (canonicalWeyl_square_charTwo A hs hp b s K j)
      (canonical_weyl_product_cube A hs hp b s K k j hkj))

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckCharTwoFoldedBraid
