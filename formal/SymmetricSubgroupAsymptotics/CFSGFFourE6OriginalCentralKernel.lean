import SymmetricSubgroupAsymptotics.CFSGFFourE6ActionCentralKernel
import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalProjection
import SymmetricSubgroupAsymptotics.CFSGPGeneratedCentralKernel

/-! The projection from the literal folded F4 matrix group to the
ORIGINAL projective model has central kernel. The first restricted-action
kernel has been proved central separately; the second centre-quotient
layer is controlled by actual p-subgroup generation and the injective
positive Sylow. No perfectness or representation faithfulness premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalCentralKernel
open CFSGFFourSerreMatrices CFSGFFourOriginalGoodSylow
open CFSGFFourE6ActionCentralKernel CFSGFFourE6OriginalProjection
open CFSGFFourE6PositiveSylow CFSGFFourE6OppositeSylow CFSGFFourE6RootSubgroups
open CFSGSerreQuadraticMatrix CFSG.Models.Chevalley

theorem foldedSylows_generate (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    (positiveSylow K p : Subgroup (canonicalElementaryGroup realizationData K)) ⊔
      (negativeSylow K p : Subgroup (canonicalElementaryGroup realizationData K)) = ⊤ := by
  let H := canonicalElementaryGroup realizationData K
  let P : Subgroup H := positiveSylow K p
  let Q : Subgroup H := negativeSylow K p
  have hpos : foldedRootGroup K false ≤ P.map H.subtype := by
    intro x hx
    refine ⟨⟨x, foldedRootGroup_le_model K false hx⟩, ?_, rfl⟩
    change (⟨x, foldedRootGroup_le_model K false hx⟩ : H) ∈
      (positiveSylow K p : Subgroup H)
    rw [positiveSylow_coe]
    exact foldedRootGroup_le_ambient K false hx
  have hneg : foldedRootGroup K true ≤ Q.map H.subtype := by
    intro x hx
    refine ⟨⟨x, foldedRootGroup_le_model K true hx⟩, ?_, rfl⟩
    change (⟨x, foldedRootGroup_le_model K true hx⟩ : H) ∈
      (negativeSylow K p : Subgroup H)
    rw [negativeSylow_coe]
    exact foldedRootGroup_le_ambient K true hx
  apply le_antisymm le_top
  apply (Subgroup.map_le_map_iff_of_injective H.subtype_injective).mp
  change (⊤ : Subgroup H).map H.subtype ≤ (P ⊔ Q).map H.subtype
  rw [Subgroup.map_sup]
  rintro x ⟨y, _, rfl⟩
  have hy : y.val ∈ foldedRootGroup K false ⊔ foldedRootGroup K true := by
    rw [foldedRootGroup_sup K]
    exact y.property
  exact (sup_le_sup hpos hneg) hy

theorem original_kernel_le_action_center (K : Type) [Field K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    (foldedToOriginal K).ker ≤ (Subgroup.center (imageGroup K)).comap (foldedToImage K) := by
  intro g hg
  change foldedToImage K g ∈ Subgroup.center (imageGroup K)
  have hi : foldedToImage K g ∈ (imageToOriginal K).ker := hg
  rwa [imageToOriginal_kernel] at hi

theorem foldedToOriginal_kernel_le_center (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] :
    (foldedToOriginal K).ker ≤ Subgroup.center (canonicalElementaryGroup realizationData K) := by
  apply CFSGPGeneratedCentralKernel.kernel_le_center_of_injective_sylow
    (foldedToImage K) (foldedToImage_kernel_le_center K)
    (foldedToOriginal K) (original_kernel_le_action_center K) (positiveSylow K p)
  · exact foldedPositiveToOriginal_injective K p
  · exact (positiveSylow K p).isPGroup'
  · exact (negativeSylow K p).isPGroup'
  · exact foldedSylows_generate K p

end SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalCentralKernel
