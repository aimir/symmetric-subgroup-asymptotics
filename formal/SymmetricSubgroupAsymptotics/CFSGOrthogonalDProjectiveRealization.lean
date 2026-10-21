import SymmetricSubgroupAsymptotics.CFSGOrthogonalDImageRealization
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDProjectiveCenter
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDElementaryEvenOrder
import SymmetricSubgroupAsymptotics.CFSGSimpleProjectiveDescent

/-! The original untransposed type-D Serre projective model is the actual
central quotient of the literal natural elementary root matrix subgroup.
All maps use the same integral tensor image. Source simplicity is used
only for the final kernel argument, with no source Lie injectivity,
named classical-group recognition, or order formula. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
open CFSG.Models.Chevalley

def sourceActionIntoElementaryRange (K : Type) [Field K] (r : ℕ) (hr : 4 ≤ r) :
    Model (CartanMatrix.D r) K →* (elementaryImageAction K r hr).range where
  toFun g := ⟨orthogonalImageRepresentation K r hr g, by
    rw [← orthogonal_action_ranges_eq K r hr]
    exact ⟨g, rfl⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ g h)

theorem sourceActionIntoElementaryRange_surjective (K : Type) [Field K] (r : ℕ) (hr : 4 ≤ r) :
    Function.Surjective (sourceActionIntoElementaryRange K r hr) := by
  intro y
  have hy : y.val ∈ (orthogonalImageRepresentation K r hr).range := by
    rw [orthogonal_action_ranges_eq K r hr]
    exact y.property
  obtain ⟨g, hg⟩ := hy
  exact ⟨g, Subtype.ext hg⟩

def sourceToElementaryProjective (K : Type) [Field K] (r : ℕ) :
    Model (CartanMatrix.D (r + 4)) K →* elementaryProjective K (r + 4) :=
  (elementaryProjectiveActionEquiv K r).symm.toMonoidHom.comp
    (sourceActionIntoElementaryRange K (r + 4) (by omega))

theorem sourceToElementaryProjective_surjective (K : Type) [Field K] (r : ℕ) :
    Function.Surjective (sourceToElementaryProjective K r) :=
  (elementaryProjectiveActionEquiv K r).symm.surjective.comp
    (sourceActionIntoElementaryRange_surjective K (r + 4) (by omega))

theorem sourceCenter_le_projectiveKernel (K : Type) [Field K] (r : ℕ) :
    Subgroup.center (Model (CartanMatrix.D (r + 4)) K) ≤
      (sourceToElementaryProjective K r).ker := by
  intro g hg
  have h := CFSGSimpleProjectiveDescent.map_mem_center
    (sourceToElementaryProjective K r) (sourceToElementaryProjective_surjective K r) g hg
  rw [elementaryProjective_center_eq_bot K r] at h
  exact Subgroup.mem_bot.mp h

def serreToElementaryProjective (K : Type) [Field K] (r : ℕ) :
    Projective (CartanMatrix.D (r + 4)) K →* elementaryProjective K (r + 4) :=
  QuotientGroup.lift (Subgroup.center (Model (CartanMatrix.D (r + 4)) K))
    (sourceToElementaryProjective K r) (sourceCenter_le_projectiveKernel K r)

theorem serreToElementaryProjective_surjective (K : Type) [Field K] (r : ℕ) :
    Function.Surjective (serreToElementaryProjective K r) := by
  intro y
  obtain ⟨g, rfl⟩ := sourceToElementaryProjective_surjective K r y
  exact ⟨(QuotientGroup.mk' (Subgroup.center
    (Model (CartanMatrix.D (r + 4)) K))) g, rfl⟩

theorem elementaryProjective_nontrivial (K : Type) [Field K] (r : ℕ) :
    Nontrivial (elementaryProjective K (r + 4)) := by
  let q := QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (r + 4)))
  apply nontrivial_of_ne (q (chainWeyl K (r + 2))) 1
  intro h
  exact chainWeyl_not_center K (r + 2) ((QuotientGroup.eq_one_iff _).mp h)

theorem serreToElementaryProjective_injective (K : Type) [Field K] (r : ℕ)
    [IsSimpleGroup (Projective (CartanMatrix.D (r + 4)) K)] :
    Function.Injective (serreToElementaryProjective K r) := by
  letI projectiveTargetNontrivial : Nontrivial (elementaryProjective K (r + 4)) :=
    elementaryProjective_nontrivial K r
  rcases (inferInstance : (serreToElementaryProjective K r).ker.Normal).eq_bot_or_eq_top with hk | hk
  · exact (serreToElementaryProjective K r).ker_eq_bot_iff.mp hk
  · have hone : serreToElementaryProjective K r = 1 := MonoidHom.ker_eq_top_iff.mp hk
    obtain ⟨y, hy⟩ := exists_ne (1 : elementaryProjective K (r + 4))
    obtain ⟨x, rfl⟩ := serreToElementaryProjective_surjective K r y
    exact (hy (by rw [hone]; rfl)).elim

def serreProjectiveEquivElementaryProjective (K : Type) [Field K] (r : ℕ)
    [IsSimpleGroup (Projective (CartanMatrix.D (r + 4)) K)] :
    Projective (CartanMatrix.D (r + 4)) K ≃* elementaryProjective K (r + 4) :=
  MulEquiv.ofBijective (serreToElementaryProjective K r)
    ⟨serreToElementaryProjective_injective K r, serreToElementaryProjective_surjective K r⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
