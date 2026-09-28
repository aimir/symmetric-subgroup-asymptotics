import SymmetricSubgroupAsymptotics.Non2UnipotentPrefixPhysicalOwner
import SymmetricSubgroupAsymptotics.Non2OriginalFusionPayloadSelection

/-!
# Original-weight estimate for the physical E7 unipotent-prefix owner

The hot and cold E7 cells are exactly the complete physical subgroups having
one certified pointing in the fixed eight-width pair menu.  This file counts
their union through the original action and every literal normal axis.  The
pointing, pair frame, quotient map, and complement are witnesses in a
proposition; they do not form an additional counted index.

The resulting row keeps the actual prefix degree of each arbitrary-axis
payload.  It is strictly forward and has exponentially small total mass.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- The literal union of the two physical E7 owner cells. -/
def E7UPOwnedPhysical
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (n : ℕ) : Set (Subgroup (Equiv.Perm (Fin n))) :=
  {H | ∃ j : Fin 2,
    e7UPPhysicalOwnerMenu hTracey hExceptional n j H}

/-- Hot/cold ownership is exactly existence of a certified physical
pointing. -/
theorem e7UPOwnedPhysical_iff_certified
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))} :
    H ∈ E7UPOwnedPhysical hTracey hExceptional n ↔
      E7UPCertifiedPhysical hTracey hExceptional n H := by
  constructor
  · rintro ⟨j, hj⟩
    cases hk : e7UPOwnerKindEquiv j with
    | hot =>
        simp only [e7UPPhysicalOwnerMenu, hk,
          E7UPOwnerKind.property] at hj
        rcases hj with ⟨i, b, e, N, J, β, hH, hcut, _⟩
        exact ⟨i, b, e, N, J, β, hH, hcut⟩
    | cold =>
        simp only [e7UPPhysicalOwnerMenu, hk,
          E7UPOwnerKind.property] at hj
        exact hj.1
  · intro hH
    rcases e7UPCertifiedPhysical_hot_or_cold
        hTracey hExceptional hH with hhot | hcold
    · refine ⟨e7UPOwnerKindEquiv.symm .hot, ?_⟩
      simpa only [e7UPPhysicalOwnerMenu, Equiv.apply_symm_apply,
        E7UPOwnerKind.property] using hhot
    · refine ⟨e7UPOwnerKindEquiv.symm .cold, ?_⟩
      simpa only [e7UPPhysicalOwnerMenu, Equiv.apply_symm_apply,
        E7UPOwnerKind.property] using hcold

/-- A displayed E7 reconstruction enters the canonical family for its
literal original action.  Replacing its displayed ambient chart by the fixed
canonical chart creates no additional label factor. -/
theorem e7UPCertifiedPhysical_cover
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (n : ℕ) (hn : 512 ≤ n)
    (H : Subgroup (Equiv.Perm (Fin n)))
    (hH : E7UPCertifiedPhysical hTracey hExceptional n H) :
    ∃ (i : ActionIndex),
      H ∈ FusionCanonicalFamily (sourceAction i)
        ((PairCountLabel.sourceDegree_le_512 i.1).trans hn)
        (fun _ => True) := by
  rcases hH with ⟨i, b, e, N, J, β, hH, _⟩
  have hdegree : 2 * pairCount i + b = n := by
    simpa only [Fintype.card_fin] using Fintype.card_congr e
  have hwidth : 2 * pairCount i ≤ n := by omega
  have hb : b = n - 2 * pairCount i := by omega
  subst b
  let L := fusionFullGoursatEncode N J β
  let K : Subgroup
      (Equiv.Perm (Fin (2 * pairCount i) ⊕
        Fin (n - 2 * pairCount i))) :=
    L.1.map (fusionOrbitAction (sourceAction i))
  have hmodel : K ∈ FusionOrbitModel (sourceAction i)
      (FusionAcceptedOrbitPredicate (sourceAction i) (fun _ => True)) := by
    refine ⟨⟨L.1, L.2, trivial⟩, rfl⟩
  have hfamily : K ∈ FusionOrbitFamily (sourceAction i)
      (FusionAcceptedOrbitPredicate (sourceAction i) (fun _ => True)) := by
    refine ⟨⟨Equiv.refl _, ⟨K, hmodel⟩⟩, ?_⟩
    exact relabelSubgroup_refl K
  have hcanonical := fusionRelabelledFamily_of_chart
    (FusionOrbitModel (sourceAction i)
      (FusionAcceptedOrbitPredicate (sourceAction i) (fun _ => True)))
    (finSumFinEquiv.trans e)
    (fusionMenuPointEquiv (pairCount i) n
      ((PairCountLabel.sourceDegree_le_512 i.1).trans hn)) K hfamily
  refine ⟨i, ?_⟩
  rw [hH]
  simpa only [E7UPOwnedPhysical, e7UPReconstruction, L, K,
    relabelSubgroup_trans] using hcanonical

/-- Exact direct row for the complete physical E7 owner union. -/
def e7UPPhysicalDirectRow
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (n m : ℕ) : ℝ :=
  non2OriginalFusionPayloadDirectRow pairCount sourceAction
    (fun i N => some (axisPayload hTracey hExceptional i N)) n m

theorem e7UPPhysicalDirectRow_nonneg
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (n m : ℕ) :
    0 ≤ e7UPPhysicalDirectRow hTracey hExceptional n m :=
  non2OriginalFusionPayloadDirectRow_nonneg pairCount sourceAction
    (fun i N => some (axisPayload hTracey hExceptional i N)) n m

theorem e7UPPhysicalDirectRow_forward
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    {n m : ℕ} (hnm : n ≤ m) :
    e7UPPhysicalDirectRow hTracey hExceptional n m = 0 :=
  non2OriginalFusionPayloadDirectRow_forward pairCount sourceAction
    (fun i N => some (axisPayload hTracey hExceptional i N))
    (fun i => PairCountLabel.pairCount_ge_24 i.1) hnm

/-- The literal hot/cold owner union is bounded by its exact original-weight
forward row. -/
theorem e7UPOwnedPhysical_direct_recurrence
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (n : ℕ) (hn : 512 ≤ n) :
    (Nat.card (E7UPOwnedPhysical hTracey hExceptional n) : ℝ) /
        exactBenchmark n ≤
      ∑ m ∈ Finset.range n,
        e7UPPhysicalDirectRow hTracey hExceptional n m *
          ordinarySubgroupRatio m := by
  apply non2OriginalFusion_payload_direct_recurrence pairCount sourceAction
    (fun i N => some (axisPayload hTracey hExceptional i N))
    (fun i => PairCountLabel.pairCount_ge_24 i.1) n
    (fun i => (PairCountLabel.sourceDegree_le_512 i.1).trans hn)
    (E7UPOwnedPhysical hTracey hExceptional n) (fun _ _ => True)
  · intro i _ _ _
    trivial
  · intro H hH
    exact e7UPCertifiedPhysical_cover hTracey hExceptional n hn H
      ((e7UPOwnedPhysical_iff_certified hTracey hExceptional).mp hH)
  · intro i N hnone J
    simp at hnone

/-- The complete E7 row has a uniform exponential deficit in the ambient
degree. -/
theorem e7UPPhysicalDirectRow_decay
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput) :
    ∃ A κ : ℝ, 0 < A ∧ 0 < κ ∧ ∀ᶠ n : ℕ in atTop,
      ∑ m ∈ Finset.range n,
        e7UPPhysicalDirectRow hTracey hExceptional n m ≤
          A * (2 : ℝ) ^ (-κ * (n : ℝ)) :=
  non2OriginalFusionPayloadDirectRow_decay pairCount sourceAction
    (fun i N => some (axisPayload hTracey hExceptional i N))
    (fun i => PairCountLabel.pairCount_ge_24 i.1)
    (fun i => PairCountLabel.pairCount_even i.1)

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
