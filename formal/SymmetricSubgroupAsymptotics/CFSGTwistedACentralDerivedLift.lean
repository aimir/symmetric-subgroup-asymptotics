import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Subgroup.Center

/-! Central ambiguity disappears on the SAME commutator subgroup.
This generic group lemma will apply to natural similitude lifts: it
does not assert the existence of those lifts or identify a named group. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedACentralDerivedLift
variable {G H : Type*} [Group G] [Group H]

def centralRatioHom (f g : G →* H)
    (hcentral : ∀ x, f x * (g x)⁻¹ ∈ Subgroup.center H) :
    G →* Subgroup.center H where
  toFun x := ⟨f x * (g x)⁻¹, hcentral x⟩
  map_one' := by
    apply Subtype.ext
    simp only [map_one, inv_one, mul_one, Subgroup.coe_one]
  map_mul' x y := by
    apply Subtype.ext
    change f (x * y) * (g (x * y))⁻¹ =
      (f x * (g x)⁻¹) * (f y * (g y)⁻¹)
    have hc : (f y * (g y)⁻¹) * (g x)⁻¹ =
        (g x)⁻¹ * (f y * (g y)⁻¹) :=
      (Subgroup.mem_center_iff.mp (hcentral y) ((g x)⁻¹)).symm
    rw [map_mul, map_mul, mul_inv_rev]
    calc
      _ = f x * ((f y * (g y)⁻¹) * (g x)⁻¹) := by simp only [mul_assoc]
      _ = f x * ((g x)⁻¹ * (f y * (g y)⁻¹)) := congrArg (fun z => f x * z) hc
      _ = _ := by simp only [mul_assoc]

theorem eq_on_commutator_of_central_ratios (f g : G →* H)
    (hcentral : ∀ x, f x * (g x)⁻¹ ∈ Subgroup.center H)
    (x : commutator G) : f x.val = g x.val := by
  letI : CommGroup (Subgroup.center H) :=
    { toGroup := (inferInstance : Group (Subgroup.center H))
      mul_comm := fun a b => mul_comm' a b }
  have hx : centralRatioHom f g hcentral x.val = 1 :=
    MonoidHom.mem_ker.mp
      (Abelianization.commutator_subset_ker (centralRatioHom f g hcentral) x.property)
  have he := congrArg (fun z : Subgroup.center H => (z : H)) hx
  change f x.val * (g x.val)⁻¹ = 1 at he
  exact mul_inv_eq_one.mp he

theorem twist_fixes_derived_lifts (τ : H →* H) (lift : G →* H)
    (hcentral : ∀ x, τ (lift x) * (lift x)⁻¹ ∈ Subgroup.center H)
    (x : commutator G) : τ (lift x.val) = lift x.val :=
  eq_on_commutator_of_central_ratios (τ.comp lift) lift hcentral x

end SymmetricSubgroupAsymptotics.CFSGTwistedACentralDerivedLift
