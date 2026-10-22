import SymmetricSubgroupAsymptotics.CFSGSemilinearFieldUniqueness

/-! The field-uniqueness theorem applies to embeddings into an arbitrary
common ambient module. This permits comparison on a two-dimensional
overlap without assuming that the two maximal spaces have equal images
as vector maps. Actual coincident rays supply the range containment. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSemilinearRayRigidity
variable {K I U : Type*} [Field K] [DecidableEq I] [AddCommGroup U] [Module K U]
local instance (s : K≃+*K) : RingHomInvPair s.toRingHom s.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv s
local instance (s : K≃+*K) : RingHomInvPair s.symm.toRingHom s.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm s
local instance (s t : K≃+*K) : RingHomCompTriple s.toRingHom t.toRingHom (s.trans t).toRingHom :=
  ⟨rfl⟩

theorem field_eq_of_embedding_rays (σ τ : K≃+*K)
    (f : (I→K)→ₛₗ[σ.toRingHom]U) (g : (I→K)→ₛₗ[τ.toRingHom]U)
    (hg : Function.Injective g) (i j : I) (hij : i≠j)
    (h : ∀w : I→K,w≠0 → ∃c : K,c≠0 ∧ f w=c•g w) : σ=τ := by
  classical
  have hr : ∀w,f w∈g.range := by
    intro w
    by_cases hw : w=0
    · simp only [hw,map_zero]
      exact g.range.zero_mem
    · obtain ⟨c,_,he⟩ := h w hw
      rw [he]
      exact g.range.smul_mem c ⟨w,rfl⟩
  let e : (I→K)≃ₛₗ[τ.toRingHom]g.range := LinearEquiv.ofInjective g hg
  let fR : (I→K)→ₛₗ[σ.toRingHom]g.range := f.codRestrict g.range hr
  let C : (I→K)→ₛₗ[(σ.trans τ.symm).toRingHom](I→K) := e.symm.toLinearMap.comp fR
  have hfix : ∀w : I→K,w≠0 → ∃c : K,c≠0 ∧ C w=c•w := by
    intro w hw
    obtain ⟨c,hc,he⟩ := h w hw
    have heR : fR w=c•e w := Subtype.ext he
    refine ⟨τ.symm c,?_,?_⟩
    · intro hz
      exact hc (τ.symm.injective (hz.trans τ.symm.map_zero.symm))
    · change e.symm (fR w)=τ.symm c•w
      rw [heR,e.symm.map_smulₛₗ,e.symm_apply_apply]
      rfl
  have hid := field_eq_id _ C i j hij hfix
  apply RingEquiv.ext
  intro a
  apply τ.symm.injective
  have hh := RingHom.congr_fun hid a
  change τ.symm (σ a)=a at hh
  exact hh.trans (τ.symm_apply_apply a).symm

end SymmetricSubgroupAsymptotics.CFSGSemilinearRayRigidity
