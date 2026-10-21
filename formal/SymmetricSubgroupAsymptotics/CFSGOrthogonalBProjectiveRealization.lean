import SymmetricSubgroupAsymptotics.CFSGOrthogonalBImageKernel
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBProjectiveCenter
import SymmetricSubgroupAsymptotics.CFSGSimpleProjectiveDescent

/-! The original B-transpose projective Serre model is equivalent to the
actual quadratic-root natural central quotient away from characteristic
two. Source simplicity is used only for the final kernel step. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
open CFSG.Models.Chevalley

def sourceActionIntoElementaryRange (K : Type) [Field K] (r : ℕ) :
    Model (CartanMatrix.B r).transpose K →* (elementaryImageAction K r).range where
  toFun g := ⟨orthogonalImageRepresentation K r g, by
    rw [← orthogonal_action_ranges_eq K r]
    exact ⟨g, rfl⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ g h)

theorem sourceActionIntoElementaryRange_surjective (K : Type) [Field K] (r : ℕ) :
    Function.Surjective (sourceActionIntoElementaryRange K r) := by
  intro y
  have hy : y.val ∈ (orthogonalImageRepresentation K r).range := by
    rw [orthogonal_action_ranges_eq K r]
    exact y.property
  obtain ⟨g, hg⟩ := hy
  exact ⟨g, Subtype.ext hg⟩

def sourceToElementaryProjective (K : Type) [Field K] (r : ℕ) (h2 : (2:K)≠0) :
    Model (CartanMatrix.B (r + 1)).transpose K →* elementaryProjective K (r + 1) :=
  (elementaryProjectiveActionEquiv K r h2).symm.toMonoidHom.comp
    (sourceActionIntoElementaryRange K (r + 1))

theorem sourceToElementaryProjective_surjective (K : Type) [Field K] (r : ℕ) (h2 : (2:K)≠0) :
    Function.Surjective (sourceToElementaryProjective K r h2) :=
  (elementaryProjectiveActionEquiv K r h2).symm.surjective.comp
    (sourceActionIntoElementaryRange_surjective K (r + 1))

theorem sourceCenter_le_projectiveKernel (K : Type) [Field K] (r : ℕ) (h2 : (2:K)≠0) :
    Subgroup.center (Model (CartanMatrix.B (r + 1)).transpose K) ≤
      (sourceToElementaryProjective K r h2).ker := by
  intro g hg
  have h := CFSGSimpleProjectiveDescent.map_mem_center
    (sourceToElementaryProjective K r h2) (sourceToElementaryProjective_surjective K r h2) g hg
  rw [elementaryProjective_center_eq_bot K r h2] at h
  exact Subgroup.mem_bot.mp h

def serreToElementaryProjective (K : Type) [Field K] (r : ℕ) (h2 : (2:K)≠0) :
    Projective (CartanMatrix.B (r + 1)).transpose K →* elementaryProjective K (r + 1) :=
  QuotientGroup.lift (Subgroup.center (Model (CartanMatrix.B (r + 1)).transpose K))
    (sourceToElementaryProjective K r h2) (sourceCenter_le_projectiveKernel K r h2)

theorem serreToElementaryProjective_surjective (K : Type) [Field K] (r : ℕ) (h2 : (2:K)≠0) :
    Function.Surjective (serreToElementaryProjective K r h2) := by
  intro y
  obtain ⟨g, rfl⟩ := sourceToElementaryProjective_surjective K r h2 y
  exact ⟨(QuotientGroup.mk' (Subgroup.center
    (Model (CartanMatrix.B (r + 1)).transpose K))) g, rfl⟩

theorem elementaryProjective_nontrivial (K : Type) [Field K] (r : ℕ) (h2 : (2:K)≠0) :
    Nontrivial (elementaryProjective K (r+1)) := by
  let u : elementaryRootGroup K (r+1) :=
    ⟨rootTransvection K (r+1) false (Fin.last r) 1,rootTransvection_mem K (r+1) false (Fin.last r) 1⟩
  let q := QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (r+1)))
  apply nontrivial_of_ne (q u) 1
  intro h
  have hu : u∈Subgroup.center (elementaryRootGroup K (r+1)) := (QuotientGroup.eq_one_iff _).mp h
  obtain ⟨c,hc⟩ := (elementaryRootGroup_center_iff_scalar K r h2 u).mp hu
  have hh := congrArg (fun M : Mat K (r+1)=>M (pos (r+1) (Fin.last r)) (middle (r+1))) hc
  have hi : ¬(Fin.last r).val+1<r+1 := by simp only [Fin.val_last];omega
  simp [u,rootTransvection_val,rootMatrix,rootSecond,positive,positiveSecond,hi,
    pos,neg,middle,Matrix.single,Matrix.one_apply] at hh

theorem serreToElementaryProjective_injective (K : Type) [Field K] (r : ℕ) (h2 : (2:K)≠0)
    [IsSimpleGroup (Projective (CartanMatrix.B (r + 1)).transpose K)] :
    Function.Injective (serreToElementaryProjective K r h2) := by
  letI projectiveTargetNontrivial : Nontrivial (elementaryProjective K (r + 1)) :=
    elementaryProjective_nontrivial K r h2
  rcases (inferInstance : (serreToElementaryProjective K r h2).ker.Normal).eq_bot_or_eq_top with hk | hk
  · exact (serreToElementaryProjective K r h2).ker_eq_bot_iff.mp hk
  · have hone : serreToElementaryProjective K r h2 = 1 := MonoidHom.ker_eq_top_iff.mp hk
    obtain ⟨y, hy⟩ := exists_ne (1 : elementaryProjective K (r + 1))
    obtain ⟨x, rfl⟩ := serreToElementaryProjective_surjective K r h2 y
    exact (hy (by rw [hone]; rfl)).elim

def serreProjectiveEquivElementaryProjective (K : Type) [Field K] (r : ℕ) (h2 : (2:K)≠0)
    [IsSimpleGroup (Projective (CartanMatrix.B (r + 1)).transpose K)] :
    Projective (CartanMatrix.B (r + 1)).transpose K ≃* elementaryProjective K (r + 1) :=
  MulEquiv.ofBijective (serreToElementaryProjective K r h2)
    ⟨serreToElementaryProjective_injective K r h2, serreToElementaryProjective_surjective K r h2⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
