import Mathlib.Algebra.Group.Action.End
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Tactic.Group
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Rigidity for a literal central extension of an additive field.
One quotient scalar different from one, acting trivially on the kernel,
eliminates every central error. No choice of cocycle or shear is needed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGCentralExtensionScalarRigidity
variable {G K : Type*} [Group G] [Field K]

theorem endomorphism_eq_id (pi : G →* Multiplicative K)
    (hpi : Function.Surjective pi) (hcentral : pi.ker ≤ Subgroup.center G)
    (f : G →* G) (hf : ∀ g, pi (f g) = pi g)
    (hfC : ∀ c : G, c ∈ pi.ker → f c = c)
    (t : MulAut G) (htC : ∀ c : G, c ∈ pi.ker → t c = c)
    (hft : ∀ g : G, f (t g) = t (f g)) (k : K) (hk : k ≠ 1)
    (ht : ∀ g : G, (pi (t g)).toAdd = k * (pi g).toAdd) : f = MonoidHom.id G := by
  have hfixed (g : G) : f (t g * g⁻¹) = t g * g⁻¹ := by
    let z := f g * g⁻¹
    have hz : z ∈ pi.ker := by
      change pi (f g * g⁻¹) = 1
      rw [map_mul, map_inv, hf, mul_inv_cancel]
    have hzg : z * g = f g := by dsimp only [z]; group
    have htfg : f (t g) = z * t g := by
      rw [hft, ← hzg, map_mul, htC z hz]
    have hcomm : (t g * g⁻¹) * z = z * (t g * g⁻¹) :=
      Subgroup.mem_center_iff.mp (hcentral hz) (t g * g⁻¹)
    rw [map_mul, map_inv, htfg, ← hzg, mul_inv_rev]
    calc
      (z * t g) * (g⁻¹ * z⁻¹) = z * (t g * g⁻¹) * z⁻¹ := by group
      _ = ((t g * g⁻¹) * z) * z⁻¹ := by rw [hcomm]
      _ = t g * g⁻¹ := by group
  apply MonoidHom.ext
  intro x
  obtain ⟨g, hg⟩ := hpi (Multiplicative.ofAdd ((pi x).toAdd / (k - 1)))
  have hg' : (pi g).toAdd = (pi x).toAdd / (k - 1) := congrArg Multiplicative.toAdd hg
  let h := t g * g⁻¹
  have hh : pi h = pi x := by
    apply Multiplicative.toAdd.injective
    dsimp only [h]
    rw [map_mul, map_inv]
    rw [toAdd_mul, toAdd_inv, ← sub_eq_add_neg]
    rw [ht, hg']
    field_simp [sub_ne_zero.mpr hk]
  have hc : h⁻¹ * x ∈ pi.ker := by
    change pi (h⁻¹ * x) = 1
    rw [map_mul, map_inv, hh, inv_mul_cancel]
  calc
    f x = f (h * (h⁻¹ * x)) := by rw [mul_inv_cancel_left]
    _ = h * (h⁻¹ * x) := by rw [map_mul, hfixed, hfC _ hc]
    _ = x := mul_inv_cancel_left _ _

end SymmetricSubgroupAsymptotics.CFSGCentralExtensionScalarRigidity
