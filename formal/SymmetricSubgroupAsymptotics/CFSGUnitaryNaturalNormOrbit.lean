import SymmetricSubgroupAsymptotics.CFSGUnitaryNaturalLastNormalization
import SymmetricSubgroupAsymptotics.CFSGUnitaryTwoAxisNorm

/-! Actual determinant-one natural fixed matrices are transitive on
each nonzero signed norm level in vector dimension at least three.
The proof composes actual pivot, torus, radical, and central-root words. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryParameters CFSGSerreOrdinaryTwists

theorem natural_unitary_pair_preserved (q : CFSG.PrimePower) (r : ℕ)
    (g : naturalFixed r q) (x y : Fin (r + 1) → q.Extension 2) :
    unitaryNaturalPair q r ((g.val.val : Mat (q.Extension 2) r) *ᵥ x)
        ((g.val.val : Mat (q.Extension 2) r) *ᵥ y) = unitaryNaturalPair q r x y :=
  hermitianPair_isometry (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r)
    (g.val.val : Mat (q.Extension 2) r) (naturalFixed_signedForm q r g) x y

theorem exists_natural_map_of_same_norm (q : CFSG.PrimePower) (s : ℕ)
    (x y : Fin (s + 3) → q.Extension 2) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : unitaryNaturalPair q (s + 2) x x = unitaryNaturalPair q (s + 2) y y) :
    ∃ g : naturalFixed (s + 2) q, (g.val.val : Mat (q.Extension 2) (s + 2)) *ᵥ x = y := by
  obtain ⟨g, a, hg⟩ := exists_natural_two_axis_normal_form q s x hx
  obtain ⟨h, b, hh⟩ := exists_natural_two_axis_normal_form q s y hy
  have hg' : (g.val.val : Mat (q.Extension 2) (s + 2)) *ᵥ x = unitaryTwoAxisVector q s a := hg
  have hh' : (h.val.val : Mat (q.Extension 2) (s + 2)) *ᵥ y = unitaryTwoAxisVector q s b := hh
  have hcan := (natural_unitary_pair_preserved q (s + 2) g x x).trans
    (hxy.trans (natural_unitary_pair_preserved q (s + 2) h y y).symm)
  simp only [hg', hh', unitaryTwoAxisVector_norm] at hcan
  obtain ⟨k, hk⟩ := exists_central_two_axis_map q s a b hcan
  refine ⟨h⁻¹ * k * g, ?_⟩
  change ((((h⁻¹).val.val : Mat (q.Extension 2) (s + 2)) *
    (k.val.val : Mat (q.Extension 2) (s + 2))) *
    (g.val.val : Mat (q.Extension 2) (s + 2))) *ᵥ x = y
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hg', hk]
  change (↑(h.val.val⁻¹) : Mat (q.Extension 2) (s + 2)) *ᵥ unitaryTwoAxisVector q s b = y
  rw [← hh', Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
