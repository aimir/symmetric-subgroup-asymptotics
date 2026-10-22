import SymmetricSubgroupAsymptotics.CFSGSemilinearRayRigidity

/-! Coincident projective actions of two semilinear equivalences have
the SAME field component in dimension at least two. This is the local
uniqueness needed to glue field components on overlapping singular spaces. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSemilinearRayRigidity
variable {K I : Type*} [Field K] [DecidableEq I]

local instance (s : K≃+*K) : RingHomInvPair s.toRingHom s.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv s
local instance (s : K≃+*K) : RingHomInvPair s.symm.toRingHom s.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm s
local instance (s t : K≃+*K) : RingHomCompTriple s.toRingHom t.toRingHom (s.trans t).toRingHom :=
  ⟨rfl⟩

theorem field_eq_of_same_rays (σ τ : K≃+*K)
    (f : (I→K)≃ₛₗ[σ.toRingHom](I→K)) (g : (I→K)≃ₛₗ[τ.toRingHom](I→K))
    (i j : I) (hij : i≠j)
    (h : ∀w : I→K,w≠0 → ∃c : K,c≠0 ∧ f w=c•g w) : σ=τ := by
  let C : (I→K)≃ₛₗ[(σ.trans τ.symm).toRingHom](I→K) := f.trans g.symm
  have hfix : ∀w : I→K,w≠0 → ∃c : K,c≠0 ∧ C w=c•w := by
    intro w hw
    obtain ⟨c,hc,he⟩ := h w hw
    refine ⟨τ.symm c,?_,?_⟩
    · intro hz
      exact hc (τ.symm.injective (hz.trans τ.symm.map_zero.symm))
    · change g.symm (f w)=τ.symm c•w
      rw [he,g.symm.map_smulₛₗ,g.symm_apply_apply]
      rfl
  have hid := field_eq_id _ C.toLinearMap i j hij hfix
  apply RingEquiv.ext
  intro a
  apply τ.symm.injective
  have hh := RingHom.congr_fun hid a
  change τ.symm (σ a)=a at hh
  exact hh.trans (τ.symm_apply_apply a).symm

end SymmetricSubgroupAsymptotics.CFSGSemilinearRayRigidity
