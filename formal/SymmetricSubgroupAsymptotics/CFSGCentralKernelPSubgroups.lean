import SymmetricSubgroupAsymptotics.CFSGCentralKernelPElements
import SymmetricSubgroupAsymptotics.CFSGDisjointSubgroupProductCard

/-! Cardinality consequences of the proved central-kernel p-element
separation, for actual p-subgroups and their literal quotient images. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGCentralKernelPElements
variable {G H : Type*} [Group G] [Group H] {p : ℕ} [Fact p.Prime]
    (f : G →* H) (P : Sylow p G)
    (hP : Function.Injective (f.comp (P : Subgroup G).subtype))
    (hker : f.ker ≤ Subgroup.center G)

include f P hP hker
theorem p_subgroup_injective (U : Subgroup G) (hU : IsPGroup p U) :
    Function.Injective (f.comp U.subtype) := by
  intro x y he
  apply Subtype.ext
  obtain ⟨a, ha⟩ := hU x
  obtain ⟨b, hb⟩ := hU y
  exact eq_of_p_elements f P hP hker x.val y.val
    ⟨a, congrArg Subtype.val ha⟩ ⟨b, congrArg Subtype.val hb⟩ he

theorem p_subgroup_card_map (U : Subgroup G) (hU : IsPGroup p U) :
    Nat.card (U.map f) = Nat.card U := by
  have hrange : (f.comp U.subtype).range = U.map f := by
    rw [MonoidHom.range_comp, U.range_subtype]
  rw [← hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective
    (p_subgroup_injective f P hP hker U hU)).toEquiv).symm

theorem disjoint_p_subgroups_card_mul_le [Finite H]
    (U V : Subgroup G) (hU : IsPGroup p U) (hV : IsPGroup p V) (hUV : U ⊓ V = ⊥) :
    Nat.card U * Nat.card V ≤ Nat.card H := by
  have hh := CFSGDisjointSubgroupProductCard.card_mul_le (U.map f) (V.map f)
    (disjoint_map f P hP hker U V hU hV hUV)
  rwa [p_subgroup_card_map f P hP hker U hU,
    p_subgroup_card_map f P hP hker V hV] at hh

end SymmetricSubgroupAsymptotics.CFSGCentralKernelPElements
