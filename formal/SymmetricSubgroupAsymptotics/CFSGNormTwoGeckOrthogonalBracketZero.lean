import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRationalAdjointStrings
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticWeylConjugationTransport

/-! The rational Serre zero bracket descends through the actual integer
operators to every coefficient ring, without dividing after reduction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrthogonalBracketZero
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGGeckSerreRepresentation
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

local notation "D" => realizationData A hs hp b s

theorem orthogonal_bracket_zero (K : Type*) [CommRing K] (i j : Fin r)
    (hij : cartan b s i j=0) :
    ⁅fieldRoot D K false i,fieldRoot D K false j⁆=0 := by
  have hZ : ⁅fieldRoot D ℤ false i,fieldRoot D ℤ false j⁆=0 := by
    apply CFSGSerreSquareZeroMatrix.integerCast_injective (b.support⊕Roots A)
    change (Int.castRingHom ℚ).mapMatrix ⁅fieldRoot D ℤ false i,fieldRoot D ℤ false j⁆=
      (Int.castRingHom ℚ).mapMatrix 0
    simpa only [Ring.lie_def,map_sub,map_mul,map_fieldRoot,map_zero] using
      CFSGNormTwoGeckRationalAdjointStrings.lie_of_cartan_zero A hs hp b s i j hij
  have hK := congrArg (Int.castRingHom K).mapMatrix hZ
  simpa only [Ring.lie_def,map_sub,map_mul,map_fieldRoot,map_zero] using hK

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrthogonalBracketZero
