import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalComplementNormalizer
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalNormalizerIntersection

/-! Literal signed simple-root subgroups generate the corresponding
original U or V. All restriction and quotient images are retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSignedGeneration
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGSerreQuadraticMatrix CFSGNormTwoGeckIntegralRealization
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoCoordinateOriginalPositiveCenter
open CFSGNormTwoCoordinateOriginalOppositeAlignment CFSGNormTwoCoordinateOriginalProjection
open CFSGNormTwoCoordinateElementaryRootParameters CFSGNormTwoCoordinateOriginalComplementNormalizer
open CFSGNormTwoCoordinateOriginalNormalizerIntersection
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ j, A j j = 2)
    (hs : A.transpose = A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j, i ≠ j → A i j ≤ 0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀
local notation "H" => ElementaryGroup A hd hs hp ho K

theorem signed_rootGroup_eq_iSup (neg : Bool) :
    rootGroup A hs hp b₀ s₀ K neg = ⨆ j, canonicalRootSubgroup D K neg j := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro x ⟨⟨j,a⟩,rfl⟩
    exact (le_iSup (fun k => canonicalRootSubgroup D K neg k) j) ⟨a,rfl⟩
  · apply iSup_le
    intro j x hx
    obtain ⟨a,rfl⟩ := hx
    exact Subgroup.subset_closure ⟨(j,a),rfl⟩

theorem signed_rootGroup_subgroupOf_eq_iSup (neg : Bool) :
    (rootGroup A hs hp b₀ s₀ K neg).subgroupOf H =
      ⨆ j, (canonicalRootSubgroup D K neg j).subgroupOf H := by
  have hroot (j : Fin r) : canonicalRootSubgroup D K neg j ≤ H := by
    rintro x ⟨a,rfl⟩
    exact (canonicalElementaryRoot D K neg j a).property
  have hwhole : rootGroup A hs hp b₀ s₀ K neg ≤ H := by
    rw [signed_rootGroup_eq_iSup]
    exact iSup_le hroot
  apply Subgroup.map_injective (H).subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le hwhole, Subgroup.map_iSup]
  simp only [Subgroup.map_subgroupOf_eq_of_le (hroot _)]
  exact signed_rootGroup_eq_iSup A hd hs hp ho K neg

theorem original_positive_eq_iSup [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) :
    originalPositive A hd hs hp ho K i = ⨆ j, originalSimpleRootGroup A hd hs hp ho K i j := by
  rw [originalPositive_eq_map, signed_rootGroup_subgroupOf_eq_iSup, Subgroup.map_iSup]
  rfl

theorem original_negative_eq_iSup [IsSimpleGroup (Projective (cartan b₀ s₀) K)] (i : Fin r) :
    originalNegative A hd hs hp ho K i = ⨆ j, originalNegativeSimpleRootGroup A hd hs hp ho K i j := by
  change ((rootGroup A hs hp b₀ s₀ K true).subgroupOf H).map
    (originalProjection A hd hs hp ho K i) = _
  rw [signed_rootGroup_subgroupOf_eq_iSup, Subgroup.map_iSup]
  rfl

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSignedGeneration
