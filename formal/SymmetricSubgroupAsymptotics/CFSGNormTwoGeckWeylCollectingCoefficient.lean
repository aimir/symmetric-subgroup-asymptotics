import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRationalWeylCollecting
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticWeylConjugationTransport

/-! The actual adjacent collecting coefficient over EVERY ring.
The rational string identity is first recovered as an integer matrix
identity, so reduction at two and three requires no division. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylCollectingCoefficient
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGGeckSerreRepresentation
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckParameterizedWeyl CFSGNormTwoGeckRationalWeylCollecting
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem weyl_conjugate_adjacent_all_rings (K : Type*) [CommRing K]
    (i j : Fin r) (hij : cartan b s i j= -1) :
    (canonicalWeyl (realizationData A hs hp b s) K i : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*
      fieldRoot (realizationData A hs hp b s) K false j*
      (((canonicalWeyl (realizationData A hs hp b s) K i)⁻¹ :
        (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ) : Matrix
          (b.support⊕Roots A) (b.support⊕Roots A) K)=
      ⁅fieldRoot (realizationData A hs hp b s) K false i,
        fieldRoot (realizationData A hs hp b s) K false j⁆ := by
  apply weyl_root_bracket_of_rational (realizationData A hs hp b s) K i j
  simpa only [parameterWeyl,canonicalWeyl,Units.val_one,inv_one] using
    weyl_conjugate_adjacent A hs hp b s i j hij

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylCollectingCoefficient
