import SymmetricSubgroupAsymptotics.CFSGUnitaryIsotropicFirstOrbit
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryProjectiveOrderStrict
import SymmetricSubgroupAsymptotics.CFSGQuotientOrbitIndex
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex

/-! The rank-three original unitary index square, all q including two.
The actual first-point orbit has at most q^6 points; the actual central
quotient has order strictly greater than q^12. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped LinearAlgebra.Projectivization

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedAUpperUnipotent CFSGProjectiveFrameCoordinates
open CFSGUnitaryHermitianPolynomial PrimitiveSocleRawStructure

theorem twistedA_rank_three_index_le (q : CFSG.PrimePower) (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.TwistedA 3 q) ell) : ell ≤ q.order ^ 6 := by
  let D := commutator (Fixed 3 q)
  let pi : naturalFixed 3 q →* CFSG.Models.TwistedA 3 q :=
    (QuotientGroup.mk' (Subgroup.center D)).comp (originalDerivedCover q 0)
  have hpi : Function.Surjective pi :=
    (QuotientGroup.mk'_surjective _).comp (originalDerivedCover_surjective q 0)
  letI := unitaryNaturalPointAction q 3
  have hker (g : naturalFixed 3 q) (hg : g ∈ pi.ker) :
      g • basisPoint (F := q.Extension 2) (0 : Fin 4) = basisPoint 0 := by
    have hz : originalDerivedCover q 0 g ∈ Subgroup.center D :=
      (QuotientGroup.eq_one_iff _).mp hg
    exact CFSGUpperProjectiveFirstPoint.upper_fixes_first_basisPoint 3 g.val.val
      (central_cover_upper q 0 g hz)
  obtain ⟨H, hH, hi⟩ := CFSGQuotientActionIndexUpper.exists_proper_subgroup_of_moved_point_orbit
    pi hpi (basisPoint (F := q.Extension 2) (0 : Fin 4)) hker
    (reversalFixed q 3) (reversal_moves_first_point q 3 (by omega))
  change H.index = Nat.card (firstPointOrbit q 3) at hi
  exact (hell.2 H hH).trans (hi.trans_le (firstPointOrbit_rank_three_card_le q))

theorem twistedA_rank_three_leastIndex_square_lt (q : CFSG.PrimePower) (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.TwistedA 3 q) ell) :
    ell ^ 2 < Nat.card (CFSG.Models.TwistedA 3 q) := by
  calc
    ell ^ 2 ≤ (q.order ^ 6) ^ 2 := Nat.pow_le_pow_left (twistedA_rank_three_index_le q ell hell) 2
    _ = q.order ^ 12 := (pow_mul _ _ _).symm
    _ < Nat.card (CFSG.Models.TwistedA 3 q) := twistedA_shifted_order_strict_lower q 0

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
