import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Algebra.Group.Subgroup.Lattice

/-! Generator identities prove centrality of an image in the SAME actual
quotient. They do not assert centrality of its preimage in the original group. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.GeneratedCentralImage
variable {G H K J : Type} [Group G] [Group H] [Group K]

theorem central_image (source : J → G)
    (hsource : Subgroup.closure (Set.range source)=⊤)
    (q : G →* H) (hq : Function.Surjective q) (kappa : K →* G)
    (hcomm : ∀ j k, q (source j)*q (kappa k)=q (kappa k)*q (source j)) :
    ∀ k : K, ∀ h : H, q (kappa k)*h=h*q (kappa k) := by
  intro k h
  obtain ⟨g,rfl⟩ := hq h
  have hle : Subgroup.closure (Set.range source)≤
      (Subgroup.centralizer {q (kappa k)}).comap q := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm j k)
  have hg : g∈Subgroup.closure (Set.range source) := by rw [hsource]; trivial
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hg)).symm

end SymmetricSubgroupAsymptotics.GeneratedCentralImage
