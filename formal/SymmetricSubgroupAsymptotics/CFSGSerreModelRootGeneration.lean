import SymmetricSubgroupAsymptotics.CFSGSerreRootOperatorInvertible
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Center

/-! Canonical actual root witnesses generate the original Model internally.
Every nontrivial onto quotient therefore has a nontrivial actual root image. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSerreModelRootGeneration
open CFSG.Models.Chevalley CFSGSerreLocalNilpotence
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (K : Type) [Field K]

def modelRoot (negative : Bool) (i : Fin n) (t : K) : Model A K :=
  ⟨rootEquiv A K negative i t, rootEquiv_mem_model A K negative i t⟩

def rootSet : Set (Model A K) := {g | ∃ negative i t, g = modelRoot A K negative i t}

theorem rootSet_generate : Subgroup.closure (rootSet A K) = ⊤ := by
  let R := Subgroup.closure (rootSet A K)
  have hmap : R.map (subgroup A K).subtype = subgroup A K := by
    apply le_antisymm
    · rintro g ⟨x, _, rfl⟩
      exact x.property
    · apply (Subgroup.closure_le _).mpr
      rintro g ⟨negative, i, t, hg⟩
      have he : g = rootEquiv A K negative i t := by
        apply LinearEquiv.toLinearMap_injective
        exact hg
      subst g
      exact ⟨modelRoot A K negative i t,
        Subgroup.subset_closure ⟨negative, i, t, rfl⟩, rfl⟩
  apply top_unique
  intro x _
  have hx : x.val ∈ R.map (subgroup A K).subtype := by
    rw [hmap]
    exact x.property
  obtain ⟨y, hy, he⟩ := hx
  have hxy : y = x := Subtype.ext he
  exact hxy ▸ hy

theorem hom_eq_one_of_root_images {G : Type*} [Group G] (f : Model A K →* G)
    (hf : ∀ negative i t, f (modelRoot A K negative i t) = 1) : f = 1 := by
  have hle : Subgroup.closure (rootSet A K) ≤ f.ker := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨negative, i, t, rfl⟩
    exact hf negative i t
  have htop : (⊤ : Subgroup (Model A K)) ≤ f.ker := by
    rw [← rootSet_generate A K]
    exact hle
  exact MonoidHom.ker_eq_top_iff.mp (top_unique htop)

theorem exists_root_image_ne_one {G : Type*} [Group G] [Nontrivial G]
    (f : Model A K →* G) (hf : Function.Surjective f) :
    ∃ negative i t, f (modelRoot A K negative i t) ≠ 1 := by
  by_contra hn
  have hkill : ∀ negative i t, f (modelRoot A K negative i t) = 1 := by
    intro negative i t
    by_contra h
    exact hn ⟨negative, i, t, h⟩
  have hone := hom_eq_one_of_root_images A K f hkill
  obtain ⟨y, hy⟩ := exists_ne (1 : G)
  obtain ⟨x, rfl⟩ := hf y
  exact hy (by rw [hone]; rfl)

theorem exists_projective_root_ne_one [Nontrivial (Projective A K)] :
    ∃ negative i t, (QuotientGroup.mk' (Subgroup.center (Model A K)))
      (modelRoot A K negative i t) ≠ 1 :=
  exists_root_image_ne_one A K (QuotientGroup.mk' (Subgroup.center (Model A K)))
    (QuotientGroup.mk'_surjective (Subgroup.center (Model A K)))

end SymmetricSubgroupAsymptotics.CFSGSerreModelRootGeneration
