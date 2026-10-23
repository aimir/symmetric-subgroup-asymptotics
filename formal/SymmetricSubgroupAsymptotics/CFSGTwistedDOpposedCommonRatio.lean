import SymmetricSubgroupAsymptotics.CFSGTwistedDOpposedPieceExtension
import SymmetricSubgroupAsymptotics.CFSGQuadraticPolarOpposedScalarCoherence
import SymmetricSubgroupAsymptotics.CFSGQuadraticMaximalCrossPairing

/-! The two actual opposed maximal spaces in the nonsplit fixed space
have one common mixed projective ratio. Their genuine maximality proves
cross nondegeneracy; no split-dimension identification is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDOpposedCommonRatio
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDMaximalSingularDimension
open CFSGTwistedDNegativeSpaceCoordinates CFSGTwistedDOpposedPieceExtension
open CFSGTwistedA2FixedField CFSGQuadraticMaximalCrossPairing
open CFSGOrthogonalDIndexQuadraticSubspacePoints

local instance (n : ℕ) (q : CFSG.PrimePower) :
    Module.Finite (fixedField q) (fixedSpace n q) := Module.Finite.of_finite

theorem cross_positive_nondegenerate (n : ℕ) (q : CFSG.PrimePower)
    (y : fixedSpace n q) (hy : y ∈ negativeSpace n q) (hy0 : y ≠ 0) :
    restrictedPairing (fixedQuadraticForm n q) (positiveSingular n q) y ≠ 0 := by
  intro hf
  obtain ⟨x, hx, _, he⟩ := opposed_pairing_one (fixedQuadraticForm n q)
    (negativeSpace n q) (positiveSpace n q) (negativeSpace_maximal n q)
    (positiveSpace_maximal n q) (positive_negative_disjoint n q).symm y hy hy0
  have hz := LinearMap.congr_fun hf ⟨x, hx⟩
  change (fixedQuadraticForm n q).polarBilin y x = 0 at hz
  exact one_ne_zero (he.symm.trans hz)

theorem cross_negative_nondegenerate (n : ℕ) (q : CFSG.PrimePower)
    (x : fixedSpace n q) (hx : x ∈ positiveSpace n q) (hx0 : x ≠ 0) :
    restrictedPairing (fixedQuadraticForm n q) (negativeSingular n q) x ≠ 0 := by
  intro hf
  obtain ⟨y, hy, _, he⟩ := opposed_pairing_one (fixedQuadraticForm n q)
    (positiveSpace n q) (negativeSpace n q) (positiveSpace_maximal n q)
    (negativeSpace_maximal n q) (positive_negative_disjoint n q) x hx hx0
  have hz := LinearMap.congr_fun hf ⟨y, hy⟩
  change (fixedQuadraticForm n q).polarBilin x y = 0 at hz
  exact one_ne_zero (he.symm.trans hz)

theorem exists_common_ratio (n : ℕ) (q : CFSG.PrimePower) (hn : 2 ≤ n)
    (f : Points (fixedQuadraticForm n q) ≃ Points (fixedQuadraticForm n q))
    (hlinear : ∀ W : Subspaces (fixedQuadraticForm n q),
      Nonempty (SemilinearPiece (fixedQuadraticForm n q) f W (RingEquiv.refl (fixedField q))))
    (hfixP : ∀ R : Points (fixedQuadraticForm n q), R.val ≤ positiveSpace n q → f R = R)
    (hfixZ : ∀ R : Points (fixedQuadraticForm n q), R.val ≤ negativeSpace n q → f R = R) :
    ∃ t : fixedField q, t ≠ 0 ∧ ∀ x y : fixedSpace n q,
      x ∈ positiveSpace n q → x ≠ 0 → y ∈ negativeSpace n q → y ≠ 0 →
      (fixedQuadraticForm n q).polarBilin y x = 0 →
      ∀ (hxy0 : x + y ≠ 0) (hQ : fixedQuadraticForm n q (x + y) = 0),
        (f (ray (fixedQuadraticForm n q) (x + y) hxy0 hQ)).val =
          Submodule.span (fixedField q) {x + t • y} := by
  exact opposed_common_ratio (fixedQuadraticForm n q) f
    (positiveSingular n q) (negativeSingular n q)
    (by change 3 ≤ Module.finrank (fixedField q) (positiveSpace n q)
        rw [positiveSpace_finrank]
        omega)
    ((negativeSpace_finrank n q).trans (positiveSpace_finrank n q).symm)
    (positive_negative_disjoint n q) (cross_positive_nondegenerate n q)
    (cross_negative_nondegenerate n q) (fun W _ => hlinear W) hfixP hfixZ

end SymmetricSubgroupAsymptotics.CFSGTwistedDOpposedCommonRatio
