import SymmetricSubgroupAsymptotics.CFSGSymplecticRootActionRange
import SymmetricSubgroupAsymptotics.CFSGSymplecticElementaryProjectiveNontrivial
import SymmetricSubgroupAsymptotics.CFSGSimpleProjectiveDescent

/-! Actual projective realization of the literal type-C Serre model as
the central quotient of the independently defined natural elementary
symplectic matrix group. The actual source simplicity is used only at
the last injectivity step. No source Lie injectivity or order formula,
nor equality of the elementary group with the full symplectic group,
is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
open CFSG.Models.Chevalley

def sourceActionIntoElementaryRange (K : Type) [Field K] (r : ℕ) :
    Model (CartanMatrix.C r).transpose K →* (elementaryImageAction K r).range where
  toFun g := ⟨symplecticImageRepresentation K r g, by
    rw [← symplectic_action_ranges_eq K r]
    exact ⟨g, rfl⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ g h)

theorem sourceActionIntoElementaryRange_surjective (K : Type) [Field K] (r : ℕ) :
    Function.Surjective (sourceActionIntoElementaryRange K r) := by
  intro y
  have hy : y.val ∈ (symplecticImageRepresentation K r).range := by
    rw [symplectic_action_ranges_eq K r]
    exact y.property
  obtain ⟨g, hg⟩ := hy
  exact ⟨g, Subtype.ext hg⟩

def sourceToElementaryProjective (K : Type) [Field K] (r : ℕ) :
    Model (CartanMatrix.C (r + 1)).transpose K →* elementaryProjective K (r + 1) :=
  (elementaryProjectiveActionEquiv K r).symm.toMonoidHom.comp
    (sourceActionIntoElementaryRange K (r + 1))

theorem sourceToElementaryProjective_surjective (K : Type) [Field K] (r : ℕ) :
    Function.Surjective (sourceToElementaryProjective K r) :=
  (elementaryProjectiveActionEquiv K r).symm.surjective.comp
    (sourceActionIntoElementaryRange_surjective K (r + 1))

theorem sourceCenter_le_projectiveKernel (K : Type) [Field K] (r : ℕ) :
    Subgroup.center (Model (CartanMatrix.C (r + 1)).transpose K) ≤
      (sourceToElementaryProjective K r).ker := by
  intro g hg
  have h := CFSGSimpleProjectiveDescent.map_mem_center
    (sourceToElementaryProjective K r) (sourceToElementaryProjective_surjective K r) g hg
  rw [elementaryProjective_center_eq_bot K r] at h
  exact Subgroup.mem_bot.mp h

def serreToElementaryProjective (K : Type) [Field K] (r : ℕ) :
    Projective (CartanMatrix.C (r + 1)).transpose K →* elementaryProjective K (r + 1) :=
  QuotientGroup.lift (Subgroup.center (Model (CartanMatrix.C (r + 1)).transpose K))
    (sourceToElementaryProjective K r) (sourceCenter_le_projectiveKernel K r)

theorem serreToElementaryProjective_surjective (K : Type) [Field K] (r : ℕ) :
    Function.Surjective (serreToElementaryProjective K r) := by
  intro y
  obtain ⟨g, rfl⟩ := sourceToElementaryProjective_surjective K r y
  exact ⟨(QuotientGroup.mk' (Subgroup.center
    (Model (CartanMatrix.C (r + 1)).transpose K))) g, rfl⟩

theorem serreToElementaryProjective_injective (K : Type) [Field K] (r : ℕ)
    [IsSimpleGroup (Projective (CartanMatrix.C (r + 1)).transpose K)] :
    Function.Injective (serreToElementaryProjective K r) := by
  letI projectiveTargetNontrivial : Nontrivial (elementaryProjective K (r + 1)) :=
    elementaryProjective_nontrivial K r
  rcases (inferInstance : (serreToElementaryProjective K r).ker.Normal).eq_bot_or_eq_top with hk | hk
  · exact (serreToElementaryProjective K r).ker_eq_bot_iff.mp hk
  · have hone : serreToElementaryProjective K r = 1 := MonoidHom.ker_eq_top_iff.mp hk
    obtain ⟨y, hy⟩ := exists_ne (1 : elementaryProjective K (r + 1))
    obtain ⟨x, rfl⟩ := serreToElementaryProjective_surjective K r y
    exact (hy (by rw [hone]; rfl)).elim

def serreProjectiveEquivElementaryProjective (K : Type) [Field K] (r : ℕ)
    [IsSimpleGroup (Projective (CartanMatrix.C (r + 1)).transpose K)] :
    Projective (CartanMatrix.C (r + 1)).transpose K ≃* elementaryProjective K (r + 1) :=
  MulEquiv.ofBijective (serreToElementaryProjective K r)
    ⟨serreToElementaryProjective_injective K r, serreToElementaryProjective_surjective K r⟩

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
