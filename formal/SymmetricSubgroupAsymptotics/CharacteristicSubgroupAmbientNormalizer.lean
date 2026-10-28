import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.Finite.Defs
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.Commutator.Basic

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CharacteristicSubgroupAmbientNormalizer

theorem normalizer_le {G : Type*} [Group G] [Finite G]
    (P : Subgroup G) (W : Subgroup P) [W.Characteristic] :
    Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer (W.map P.subtype : Set G) := by
  intro g hg
  let α : MulAut P := P.normalizerMonoidHom ⟨g, hg⟩
  have heq : W.map α.toMonoidHom = W :=
    Subgroup.characteristic_iff_map_eq.mp inferInstance α
  apply Subgroup.mem_normalizer_fintype
  rintro x ⟨w, hw, rfl⟩
  refine ⟨α w, ?_, rfl⟩
  have hm : α w ∈ W.map α.toMonoidHom := ⟨w, hw, rfl⟩
  rwa [heq] at hm

theorem center_inf_derived_characteristic {G : Type*} [Group G] :
    (Subgroup.center G ⊓ commutator G).Characteristic := by
  apply Subgroup.characteristic_iff_map_eq.mpr
  intro α
  rw [Subgroup.map_inf _ _ _ α.injective,
    Subgroup.characteristic_iff_map_eq.mp (inferInstance : (Subgroup.center G).Characteristic) α,
    Subgroup.characteristic_iff_map_eq.mp (inferInstance : (commutator G).Characteristic) α]

end SymmetricSubgroupAsymptotics.CharacteristicSubgroupAmbientNormalizer
