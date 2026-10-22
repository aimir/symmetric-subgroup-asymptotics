import Mathlib.GroupTheory.Coset.Card
import Mathlib.Tactic.Group

/-! A product of literal subgroups with trivial intersection has the
full product cardinality inside the ambient group. No normality needed. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGDisjointSubgroupProductCard
variable {G : Type*} [Group G]

theorem product_injective (U V : Subgroup G) (hUV : U ⊓ V = ⊥) :
    Function.Injective (fun x : U × V => (x.1.val : G) * x.2.val) := by
  rintro ⟨u, v⟩ ⟨u', v'⟩ he
  change (u.val : G) * v.val = u'.val * v'.val at he
  have hd : (u'.val : G)⁻¹ * u.val = v'.val * v.val⁻¹ := by
    calc
      _ = u'.val⁻¹ * (u.val * v.val) * v.val⁻¹ := by group
      _ = u'.val⁻¹ * (u'.val * v'.val) * v.val⁻¹ := by rw [he]
      _ = _ := by group
  have hm : u'.val⁻¹ * u.val ∈ U ⊓ V :=
    ⟨U.mul_mem (U.inv_mem u'.property) u.property,
      hd ▸ V.mul_mem v'.property (V.inv_mem v.property)⟩
  have hone : u'.val⁻¹ * u.val = 1 := by simpa only [hUV, Subgroup.mem_bot] using hm
  have hu : u = u' := Subtype.ext (inv_mul_eq_one.mp hone).symm
  have hv : v = v' := by
    apply Subtype.ext
    have h := he
    rw [hu] at h
    exact mul_left_cancel h
  exact Prod.ext hu hv

theorem card_mul_le [Finite G] (U V : Subgroup G) (hUV : U ⊓ V = ⊥) :
    Nat.card U * Nat.card V ≤ Nat.card G := by
  simpa only [Nat.card_prod] using Nat.card_le_card_of_injective _ (product_injective U V hUV)

end SymmetricSubgroupAsymptotics.CFSGDisjointSubgroupProductCard
