import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryDerivedCover
import SymmetricSubgroupAsymptotics.CFSGUpperProjectiveFirstPoint
import SymmetricSubgroupAsymptotics.CFSGQuotientActionIndexUpper
import SymmetricSubgroupAsymptotics.External.CFSG.Models.LieFamilies

/-! A proper subgroup of the ORIGINAL unitary central quotient, with
index at most the number of natural projective points. The actual
surjective matrix cover and its central kernel are retained. Full point
transitivity and named-unitary recognition are unnecessary. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped LinearAlgebra.Projectivization Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGProjectiveLinearPointAction CFSGProjectiveFrameCoordinates

abbrev unitaryNaturalPoints (q : CFSG.PrimePower) (r : ℕ) :=
  Projectivization (q.Extension 2) (Fin (r + 1) → q.Extension 2)

abbrev unitaryNaturalPointAction (q : CFSG.PrimePower) (r : ℕ) :
    MulAction (naturalFixed r q) (unitaryNaturalPoints q r) :=
  MulAction.compHom _ (linearEquiv.toMonoidHom.comp (fixedMatrixHom q r))

theorem reversal_moves_first_point (q : CFSG.PrimePower) (r : ℕ) (hr : 1 ≤ r) :
    letI := unitaryNaturalPointAction q r
    reversalFixed q r • basisPoint (F := q.Extension 2) (0 : Fin (r + 1)) ≠ basisPoint 0 := by
  letI := unitaryNaturalPointAction q r
  intro h
  change linearEquiv (signedReversalUnit (q.Extension 2) r) •
    basisPoint (F := q.Extension 2) (0 : Fin (r + 1)) =
      basisPoint (F := q.Extension 2) (0 : Fin (r + 1)) at h
  rw [basisPoint, Projectivization.smul_mk] at h
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' (q.Extension 2) _ _ _ _).mp h
  change a • Pi.single (0 : Fin (r + 1)) 1 =
    (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r) *ᵥ Pi.single 0 1 at ha
  rw [Matrix.mulVec_single_one] at ha
  have he := congrFun ha (Fin.last r)
  have hn : (Fin.last r : Fin (r + 1)) ≠ 0 := by
    intro hh
    have := congrArg (fun i : Fin (r + 1) => i.val) hh
    change r = 0 at this
    omega
  have hz : (-1 : q.Extension 2) ^ r = 0 := by
    simpa [Matrix.col, signedReversalUnit_apply, Fin.rev, signWeight,
      Pi.single_apply, hn] using he.symm
  exact (pow_ne_zero r (neg_ne_zero.mpr one_ne_zero)) hz

theorem twistedA_shifted_exists_proper_subgroup_point_index (q : CFSG.PrimePower) (s : ℕ) :
    ∃ H : Subgroup (CFSG.Models.TwistedA (s + 3) q), H ≠ ⊤ ∧
      H.index ≤ Nat.card (unitaryNaturalPoints q (s + 3)) := by
  let D := commutator (Fixed (s + 3) q)
  let pi : naturalFixed (s + 3) q →* CFSG.Models.TwistedA (s + 3) q :=
    (QuotientGroup.mk' (Subgroup.center D)).comp (originalDerivedCover q s)
  have hpi : Function.Surjective pi :=
    (QuotientGroup.mk'_surjective _).comp (originalDerivedCover_surjective q s)
  letI := unitaryNaturalPointAction q (s + 3)
  apply CFSGQuotientActionIndexUpper.exists_proper_subgroup_of_moved_point
    pi hpi (basisPoint (F := q.Extension 2) (0 : Fin (s + 4))) ?_
    (reversalFixed q (s + 3)) (reversal_moves_first_point q (s + 3) (by omega))
  intro g hg
  have hz : originalDerivedCover q s g ∈ Subgroup.center D :=
    (QuotientGroup.eq_one_iff _).mp hg
  exact CFSGUpperProjectiveFirstPoint.upper_fixes_first_basisPoint (s + 3) g.val.val
    (central_cover_upper q s g hz)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
