import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativePivots
import SymmetricSubgroupAsymptotics.CFSGTwistedDSingularNegativeHalf
import SymmetricSubgroupAsymptotics.CFSGTwistedDNegativeForkAction
import SymmetricSubgroupAsymptotics.CFSGTwistedDDerivedNegativePairedRoots

/-! Every nonzero singular fixed vector acquires an untouched negative pivot by literal relative-root words. The larger Derived-preimage orbit is not used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeNegativeSupport
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGSerreOrdinaryTwists CFSGTwistedDNaturalQuadraticTwist
open CFSGOrthogonalDIndexBundledQuadratic CFSGTwistedDDerivedPairedRoots
open CFSGTwistedDRelativePivots CFSGTwistedDPairedRootImages
open CFSGTwistedDRelativeChainLift

theorem exists_negative_support (s : ℕ) (q : CFSG.PrimePower)
    (v : Index (s + 4) → q.Extension 2)
    (hv : vectorTwist (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2) v = v)
    (hQ : splitQuadraticForm (q.Extension 2) (s + 4) v = 0) (hv0 : v ≠ 0) :
    ∃ u : relativePreimage s q, ∃ i : Fin (s + 3),
      ((u.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v) (Sum.inr i.castSucc) ≠ 0 := by
  by_cases hn : ∃ i : Fin (s + 3), v (Sum.inr i.castSucc) ≠ 0
  · refine ⟨1, ?_⟩
    change ∃ i : Fin (s + 3), ((1 : Mat (q.Extension 2) (s + 4)) *ᵥ v)
      (Sum.inr i.castSucc) ≠ 0
    simpa only [Matrix.one_mulVec] using hn
  have hzero : ∀ i : Fin (s + 3), v (Sum.inr i.castSucc) = 0 := by
    intro i
    by_contra hi
    exact hn ⟨i, hi⟩
  obtain ⟨hl, hz⟩ := CFSGTwistedDSingularNegativeHalf.vanishing_negative_half
    (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2) v hv hQ hzero
  have hp : ∃ i : Fin (s + 3), v (Sum.inl i.castSucc) ≠ 0 := by
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
  obtain ⟨a, hap, haz, hal, haf⟩ := exists_positive_pivot s q v hv hp hz hl
  let w := (a.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v
  let b : relativePreimage s q :=
    ⟨pairedNaturalRoot s q true 1,
      CFSGTwistedDRelativeChainLift.paired_mem s q true 1⟩
  have hb : ((b.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ w)
      (Sum.inr (pen (s + 2))) = -1 := by
    change (((pairedNaturalRoot s q true 1).val : Mat (q.Extension 2) (s + 4)) *ᵥ w)
      (Sum.inr (pen (s + 2))) = -1
    rw [CFSGTwistedDNegativeForkAction.negative_one_pen]
    have hnp : w (Sum.inr (pen (s + 2))) = 0 := congrFun haz (pen (s + 2))
    have hnl : w (Sum.inr (last (s + 2))) = 0 := congrFun haz (last (s + 2))
    have hwlast : w (Sum.inl (last (s + 2))) = 0 := hal
    have hwpen : w (Sum.inl (pen (s + 2))) = 1 := hap
    rw [hnp, hnl, hwlast, hwpen]
    ring
  let u : relativePreimage s q := b * a
  have he : (u.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v =
      (b.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ w := by
    change (((b.val.val * a.val.val : (Mat (q.Extension 2) (s + 4))ˣ) :
      Mat (q.Extension 2) (s + 4)) *ᵥ v) = _
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
  refine ⟨u, Fin.last (s + 2), ?_⟩
  change ((u.val.val : Mat (q.Extension 2) (s + 4)) *ᵥ v)
    (Sum.inr (pen (s + 2))) ≠ 0
  rw [he, hb]
  exact neg_ne_zero.mpr one_ne_zero

end SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeNegativeSupport
