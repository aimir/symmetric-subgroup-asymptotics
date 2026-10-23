import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckAdjacentWeylConjugacy

/-! A narrow Cartan-entry interface to the integral Weyl-square sign.
Keeping the rational pairing conversion here avoids reducing the whole
adjacent collecting packet while elaborating a root-unit equality. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckAdjacentCartanSign
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGGeckSerreRepresentation
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckAdjacentWeylConjugacy
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem adjacent_cartan_square_sign (i j : Fin r) (hji : cartan b s j i= -1)
    (K : Type) [CommRing K] (neg : Bool) (a : K) :
    (canonicalWeyl (realizationData A hs hp b s) K i)^2*
      canonicalRoot (realizationData A hs hp b s) K neg j a=
    canonicalRoot (realizationData A hs hp b s) K neg j (-a)*
      (canonicalWeyl (realizationData A hs hp b s) K i)^2 := by
  have hc : cartan b s j i=integerPairing A (s i : Roots A).val (s j : Roots A).val := by
    apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → ℚ))
    change algebraMap ℤ ℚ (b.cartanMatrixIn ℤ (s i) (s j)) = _
    rw [RootPairing.Base.algebraMap_cartanMatrixIn_apply,pairing_cast]
  exact canonical_adjacent_conjugacy A hs hp b s i j (hc.symm.trans hji) K neg a

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckAdjacentCartanSign
