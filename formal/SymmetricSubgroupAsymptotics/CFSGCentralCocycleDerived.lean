import SymmetricSubgroupAsymptotics.CFSGCentralCocyclePGroup
import Mathlib.GroupTheory.Abelianization.Defs

/-! A central difference vanishes over a derived image whenever it
vanishes on the actual kernel. This is ordinary commutator lifting, with
no p-group, splitting, or fixed-representative premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGCentralCocycleDerived
variable {E J : Type*} [Group E] [Group J]

theorem fixed_over_commutator (alpha : MulAut E) (L : Subgroup E)
    (hcentral : ∀ u : L, u.val⁻¹ * alpha u.val ∈ Subgroup.center E)
    (f : L →* J) (hf : Function.Surjective f)
    (hker : ∀ u : L, f u = 1 → alpha u.val = u.val)
    (u : L) (hu : f u ∈ commutator J) : alpha u.val = u.val := by
  letI : CommGroup (Subgroup.center E) :=
    { (inferInstance : Group (Subgroup.center E)) with
      mul_comm := fun a b => Subtype.ext ((Subgroup.mem_center_iff.mp a.property) b.val).symm }
  let c : L →* Subgroup.center E :=
    CFSGCentralCocyclePGroup.centralDifferenceHom alpha L hcentral
  have hcomm : commutator L ≤ c.ker := Abelianization.commutator_subset_ker c
  have hmap : (commutator L).map f = commutator J := by
    simp only [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective f hf]
  rw [← hmap] at hu
  obtain ⟨v, hv, hvu⟩ := hu
  have hcv : c v = 1 := hcomm hv
  have hfuv : f (u * v⁻¹) = 1 := by
    rw [map_mul, map_inv, hvu, mul_inv_cancel]
  have hfix := hker (u * v⁻¹) hfuv
  change alpha (u.val * v.val⁻¹) = u.val * v.val⁻¹ at hfix
  have hcuv : c (u * v⁻¹) = 1 := by
    apply Subtype.ext
    change (u.val * v.val⁻¹)⁻¹ * alpha (u.val * v.val⁻¹) = 1
    rw [hfix, inv_mul_cancel]
  have hcu : c u = 1 := by
    rw [map_mul, map_inv, hcv, inv_one, mul_one] at hcuv
    exact hcuv
  have hh : u.val⁻¹ * alpha u.val = 1 := congrArg Subtype.val hcu
  exact (inv_mul_eq_one.mp hh).symm

end SymmetricSubgroupAsymptotics.CFSGCentralCocycleDerived
