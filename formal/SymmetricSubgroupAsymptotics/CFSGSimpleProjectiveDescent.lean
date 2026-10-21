import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.Subgroup.Simple

/-! An onto homomorphism descends through the actual centres. If the
source's actual central quotient is simple and the target's is nontrivial,
that descended map is an equivalence. No source Lie-algebra faithfulness
or order comparison is required. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSimpleProjectiveDescent
variable {G H : Type*} [Group G] [Group H] (f : G →* H) (hf : Function.Surjective f)
include hf

theorem map_mem_center (g : G) (hg : g ∈ Subgroup.center G) : f g ∈ Subgroup.center H := by
  apply Subgroup.mem_center_iff.mpr
  intro y
  obtain ⟨x, rfl⟩ := hf y
  simpa only [map_mul] using congrArg f ((Subgroup.mem_center_iff.mp hg) x)

theorem center_le_projective_kernel :
    Subgroup.center G ≤ ((QuotientGroup.mk' (Subgroup.center H)).comp f).ker := by
  intro g hg
  change (QuotientGroup.mk' (Subgroup.center H)) (f g) = 1
  exact (QuotientGroup.eq_one_iff (f g)).mpr (map_mem_center f hf g hg)

def projectiveMap : G ⧸ Subgroup.center G →* H ⧸ Subgroup.center H :=
  QuotientGroup.lift (Subgroup.center G)
    ((QuotientGroup.mk' (Subgroup.center H)).comp f) (center_le_projective_kernel f hf)

@[simp] theorem projectiveMap_mk (g : G) :
    projectiveMap f hf ((QuotientGroup.mk' (Subgroup.center G)) g) =
      (QuotientGroup.mk' (Subgroup.center H)) (f g) := rfl

theorem projectiveMap_surjective : Function.Surjective (projectiveMap f hf) := by
  intro y
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center H) y
  obtain ⟨g, rfl⟩ := hf h
  exact ⟨(QuotientGroup.mk' (Subgroup.center G)) g, rfl⟩

theorem projectiveMap_injective [IsSimpleGroup (G ⧸ Subgroup.center G)]
    [Nontrivial (H ⧸ Subgroup.center H)] : Function.Injective (projectiveMap f hf) := by
  rcases (inferInstance : (projectiveMap f hf).ker.Normal).eq_bot_or_eq_top with hk | hk
  · exact (projectiveMap f hf).ker_eq_bot_iff.mp hk
  · have hone : projectiveMap f hf = 1 := MonoidHom.ker_eq_top_iff.mp hk
    obtain ⟨y, hy⟩ := exists_ne (1 : H ⧸ Subgroup.center H)
    obtain ⟨x, rfl⟩ := projectiveMap_surjective f hf y
    exact (hy (by rw [hone]; rfl)).elim

def projectiveEquivOfSimple [IsSimpleGroup (G ⧸ Subgroup.center G)]
    [Nontrivial (H ⧸ Subgroup.center H)] :
    G ⧸ Subgroup.center G ≃* H ⧸ Subgroup.center H :=
  MulEquiv.ofBijective (projectiveMap f hf)
    ⟨projectiveMap_injective f hf, projectiveMap_surjective f hf⟩

end SymmetricSubgroupAsymptotics.CFSGSimpleProjectiveDescent
