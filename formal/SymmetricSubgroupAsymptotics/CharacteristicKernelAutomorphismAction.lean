import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Center

/-! A surjective homomorphism with characteristic kernel transports all
actual source automorphisms to its target. This is descent through the
proved kernel, not a lift of automorphisms from the quotient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CharacteristicKernelAutomorphismAction

variable {N V : Type*} [Group N] [Group V]
variable (π : N →* V) (hπ : Function.Surjective π) [π.ker.Characteristic]

def automorphism (f : MulAut N) : MulAut V :=
  let e := QuotientGroup.quotientKerEquivOfSurjective π hπ
  (e.symm.trans (QuotientGroup.congr π.ker π.ker f
    (Subgroup.characteristic_iff_map_eq.mp inferInstance f))).trans e

theorem automorphism_apply (f : MulAut N) (u : N) :
    automorphism π hπ f (π u) = π (f u) := by
  let e := QuotientGroup.quotientKerEquivOfSurjective π hπ
  have he : e (QuotientGroup.mk' π.ker u) = π u := rfl
  change e (QuotientGroup.congr π.ker π.ker f
    (Subgroup.characteristic_iff_map_eq.mp inferInstance f) (e.symm (π u))) = π (f u)
  rw [←he,e.symm_apply_apply]
  rfl

def action : MulAut N →* MulAut V where
  toFun := automorphism π hπ
  map_one' := by
    apply MulEquiv.ext
    intro v
    obtain ⟨u,rfl⟩ := hπ v
    rw [automorphism_apply]
    rfl
  map_mul' f g := by
    apply MulEquiv.ext
    intro v
    obtain ⟨u,rfl⟩ := hπ v
    change automorphism π hπ (f*g) (π u) =
      automorphism π hπ f (automorphism π hπ g (π u))
    rw [automorphism_apply,automorphism_apply,automorphism_apply]
    rfl

end SymmetricSubgroupAsymptotics.CharacteristicKernelAutomorphismAction
