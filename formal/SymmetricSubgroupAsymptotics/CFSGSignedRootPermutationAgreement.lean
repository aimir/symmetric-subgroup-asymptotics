import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Commute.Hom

/-! Opposite simple-root permutations are the same whenever distinct
indices commute and equal indices have a noncommuting witness. This is
a group-theoretic consumer of the actual signed-root relations. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSignedRootPermutationAgreement
variable {G I P : Type*} [Group G] [Group P]

theorem permutations_agree (u v : I → P →* G)
    (hcross : ∀ i j, i ≠ j → ∀ a b, Commute (u i a) (v j b))
    (hdiag : ∀ i, ∃ a b, ¬ Commute (u i a) (v i b))
    (f : MulAut G) (σ τ : Equiv.Perm I)
    (hu : ∀ i, (u i).range.map f.toMonoidHom = (u (σ i)).range)
    (hv : ∀ i, (v i).range.map f.toMonoidHom = (v (τ i)).range) : σ = τ := by
  classical
  ext i
  let j := τ.symm (σ i)
  have hτ : τ j = σ i := τ.apply_symm_apply _
  by_contra hne
  have hij : i ≠ j := by
    intro he
    exact hne ((congrArg τ he).trans hτ).symm
  obtain ⟨a, b, hab⟩ := hdiag (σ i)
  have hua : u (σ i) a ∈ (u i).range.map f.toMonoidHom := by
    rw [hu]
    exact ⟨a, rfl⟩
  have hvb : v (σ i) b ∈ (v j).range.map f.toMonoidHom := by
    rw [hv, hτ]
    exact ⟨b, rfl⟩
  rcases hua with ⟨x, ⟨a', rfl⟩, ha⟩
  rcases hvb with ⟨y, ⟨b', rfl⟩, hb⟩
  apply hab
  have he := (hcross i j hij a' b').map f.toMonoidHom
  simpa only [ha, hb] using he

end SymmetricSubgroupAsymptotics.CFSGSignedRootPermutationAgreement
