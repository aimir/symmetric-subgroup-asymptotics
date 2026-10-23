import SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankPivots
import SymmetricSubgroupAsymptotics.CFSGTwistedDSingularNegativeHalf
import SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankNegativeForkAction

/-! Literal relative-root negative support in every rank at least three. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankNegativeSupport
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGSerreOrdinaryTwists CFSGTwistedDNaturalQuadraticTwist
open CFSGOrthogonalDIndexBundledQuadratic CFSGTwistedDRelativeElementaryGroup
open CFSGTwistedDAllRankPivots

theorem exists_negative_support (n : ℕ) (q : CFSG.PrimePower)
    (v : Index (n + 3) → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) (n + 1) (definingFieldAutomorphism q 2) v = v)
    (hQ : splitQuadraticForm (q.Extension 2) (n + 3) v = 0) (hv0 : v ≠ 0) :
    ∃ u : relativeRootGroup (n + 1) q, ∃ i : Fin (n + 2),
      ((u.val : Mat (q.Extension 2) (n + 3)) *ᵥ v) (Sum.inr i.castSucc) ≠ 0 := by
  by_cases hn : ∃ i : Fin (n + 2), v (Sum.inr i.castSucc) ≠ 0
  · refine ⟨1, ?_⟩
    change ∃ i : Fin (n + 2), ((1 : Mat (q.Extension 2) (n + 3)) *ᵥ v)
      (Sum.inr i.castSucc) ≠ 0
    simpa only [Matrix.one_mulVec] using hn
  have hzero : ∀ i : Fin (n + 2), v (Sum.inr i.castSucc) = 0 := by
    intro i
    by_contra hi
    exact hn ⟨i, hi⟩
  obtain ⟨hl, hz⟩ := CFSGTwistedDSingularNegativeHalf.vanishing_negative_half
    (q.Extension 2) (n + 1) (definingFieldAutomorphism q 2) v hv hQ hzero
  have hp : ∃ i : Fin (n + 2), v (Sum.inl i.castSucc) ≠ 0 := by
    by_contra h
    apply hv0
    funext x
    cases x with
    | inl i =>
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · by_contra hj
        exact h ⟨j, hj⟩
      · exact hl
    | inr i => exact congrFun hz i
  obtain ⟨a, hap, haz, hal, haf⟩ := exists_positive_pivot n q v hv hp hz hl
  let w := (a.val : Mat (q.Extension 2) (n + 3)) *ᵥ v
  let b : relativeRootGroup (n + 1) q :=
    ⟨pairedRoot (n + 1) q true 1,
      CFSGTwistedDRelativeElementaryGroup.paired_mem (n + 1) q true 1⟩
  have hb : ((b.val : Mat (q.Extension 2) (n + 3)) *ᵥ w)
      (Sum.inr (pen (n + 1))) = -1 := by
    change ((pairedRoot (n + 1) q true 1 : Mat (q.Extension 2) (n + 3)) *ᵥ w)
      (Sum.inr (pen (n + 1))) = -1
    rw [CFSGTwistedDAllRankNegativeForkAction.negative_one_pen]
    have hnp : w (Sum.inr (pen (n + 1))) = 0 := congrFun haz (pen (n + 1))
    have hnl : w (Sum.inr (last (n + 1))) = 0 := congrFun haz (last (n + 1))
    have hwlast : w (Sum.inl (last (n + 1))) = 0 := hal
    have hwpen : w (Sum.inl (pen (n + 1))) = 1 := hap
    rw [hnp, hnl, hwlast, hwpen]
    ring
  let u : relativeRootGroup (n + 1) q := b * a
  have he : (u.val : Mat (q.Extension 2) (n + 3)) *ᵥ v =
      (b.val : Mat (q.Extension 2) (n + 3)) *ᵥ w := by
    change (((b.val * a.val : (Mat (q.Extension 2) (n + 3))ˣ) :
      Mat (q.Extension 2) (n + 3)) *ᵥ v) = _
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
  refine ⟨u, Fin.last (n + 1), ?_⟩
  change ((u.val : Mat (q.Extension 2) (n + 3)) *ᵥ v)
    (Sum.inr (pen (n + 1))) ≠ 0
  rw [he, hb]
  exact neg_ne_zero.mpr one_ne_zero

end SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankNegativeSupport
