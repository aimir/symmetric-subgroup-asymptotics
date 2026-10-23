import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoDerivedCover
import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoOrbitPolynomial
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryProjectivePointIndex
import SymmetricSubgroupAsymptotics.CFSGQuotientOrbitIndex
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawSimpleIndex

/-! The actual rank-two original quotient has a proper point
stabilizer whose index satisfies ell (q-1) <= q^4.  The quotient kernel
is discharged by its proved triangular natural lifts. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped LinearAlgebra.Projectivization

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedAUpperUnipotent CFSGProjectiveFrameCoordinates
open CFSGUnitaryHermitianPolynomial PrimitiveSocleRawStructure

theorem twistedA_rank_two_index_mul_le (q : CFSG.PrimePower) (hq : 3 ≤ q.order) (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.TwistedA 2 q) ell) :
    ell * (q.order - 1) ≤ q.order ^ 4 := by
  let D := commutator (Fixed 2 q)
  let pi : naturalFixed 2 q →* CFSG.Models.TwistedA 2 q :=
    (QuotientGroup.mk' (Subgroup.center D)).comp (rankTwoDerivedCover q hq)
  have hpi : Function.Surjective pi :=
    (QuotientGroup.mk'_surjective _).comp (rankTwoDerivedCover_surjective q hq)
  letI := unitaryNaturalPointAction q 2
  have hker (g : naturalFixed 2 q) (hg : g ∈ pi.ker) :
      g • basisPoint (F := q.Extension 2) (0 : Fin 3) = basisPoint 0 := by
    have hz : rankTwoDerivedCover q hq g ∈ Subgroup.center D :=
      (QuotientGroup.eq_one_iff _).mp hg
    exact CFSGUpperProjectiveFirstPoint.upper_fixes_first_basisPoint 2 g.val.val
      (rankTwo_central_cover_upper q hq g hz)
  obtain ⟨H, hH, hi⟩ := CFSGQuotientActionIndexUpper.exists_proper_subgroup_of_moved_point_orbit
    pi hpi (basisPoint (F := q.Extension 2) (0 : Fin 3)) hker
    (reversalFixed q 2) (reversal_moves_first_point q 2 (by decide))
  change H.index = Nat.card (firstPointOrbit q 2) at hi
  exact (Nat.mul_le_mul_right (q.order - 1) ((hell.2 H hH).trans_eq hi)).trans
    (firstPointOrbit_rank_two_card_mul_le q)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
