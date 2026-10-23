import SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankZeroLastNormalization
import SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankZeroLastReduction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDAllRankQuadraticPreservation
import SymmetricSubgroupAsymptotics.CFSGTwistedDRankTwoSingularOrbit

/-! Literal relative-root singular-vector normalization in all ranks
at least three, and the exact all-rank dispatcher with the genuine
rank-two norm/Weyl proof. No fixed-group presentation is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankSingularOrbit
open CFSGOrthogonalDSerreMatrices CFSGTwistedDNaturalQuadraticTwist
open CFSGSerreOrdinaryTwists CFSGTwistedDRelativeElementaryGroup
open CFSGOrthogonalDIndexBundledQuadratic

theorem exists_normalize_singular (n : ℕ) (q : CFSG.PrimePower)
    (v : Index (n + 3) → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) (n + 1) (definingFieldAutomorphism q 2) v = v)
    (hQ : splitQuadraticForm (q.Extension 2) (n + 3) v = 0) (hv0 : v ≠ 0) :
    ∃ u : relativeRootGroup (n + 1) q,
      (u.val : Mat (q.Extension 2) (n + 3)) *ᵥ v = Pi.single (Sum.inl 0) 1 := by
  obtain ⟨a, hap, han⟩ :=
    CFSGTwistedDAllRankZeroLastReduction.exists_clear_last_pair n q v hv hQ hv0
  let w := (a.val : Mat (q.Extension 2) (n + 3)) *ᵥ v
  have hw : vectorTwist (q.Extension 2) (n + 1) (definingFieldAutomorphism q 2) w = w :=
    CFSGTwistedDAllRankPivots.preserves_fixed n q a v hv
  have hwQ : splitQuadraticForm (q.Extension 2) (n + 3) w = 0 := by
    rw [splitQuadraticForm_apply]
    have hqv : CFSGOrthogonalDIndexQuadraticForm.splitQ (q.Extension 2) v = 0 :=
      (splitQuadraticForm_apply (q.Extension 2) (n + 3) v).symm.trans hQ
    exact (CFSGOrthogonalDAllRankQuadraticPreservation.elementary_preserves
      (q.Extension 2) (n + 1) ⟨a.val, relativeRootGroup_le_elementary (n + 1) q a.property⟩ v).trans hqv
  have hw0 : w ≠ 0 := by
    intro hz
    apply hv0
    have he := congrArg (fun x : Index (n + 3) → q.Extension 2 =>
      (↑(a.val⁻¹) : Mat (q.Extension 2) (n + 3)) *ᵥ x) hz
    change (↑(a.val⁻¹) : Mat (q.Extension 2) (n + 3)) *ᵥ
      ((a.val : Mat (q.Extension 2) (n + 3)) *ᵥ v) =
        (↑(a.val⁻¹) : Mat (q.Extension 2) (n + 3)) *ᵥ 0 at he
    simpa only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec,
      Matrix.mulVec_zero] using he
  obtain ⟨b, hb⟩ := CFSGTwistedDAllRankZeroLastNormalization.exists_normalize
    n q w hw hap han hwQ hw0
  refine ⟨b * a, ?_⟩
  change ((b.val : Mat (q.Extension 2) (n + 3)) *
    (a.val : Mat (q.Extension 2) (n + 3))) *ᵥ v = _
  rw [← Matrix.mulVec_mulVec]
  exact hb

theorem exists_normalize_all (n : ℕ) (q : CFSG.PrimePower)
    (v : Index (n + 2) → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) n (definingFieldAutomorphism q 2) v = v)
    (hQ : splitQuadraticForm (q.Extension 2) (n + 2) v = 0) (hv0 : v ≠ 0) :
    ∃ u : relativeRootGroup n q,
      (u.val : Mat (q.Extension 2) (n + 2)) *ᵥ v = Pi.single (Sum.inl 0) 1 := by
  cases n with
  | zero =>
    exact CFSGTwistedDRankTwoSingularOrbit.exists_normalize_singular q v hv
      ((splitQuadraticForm_apply (q.Extension 2) 2 v).symm.trans hQ) hv0
  | succ n => exact exists_normalize_singular n q v hv hQ hv0

end SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankSingularOrbit
