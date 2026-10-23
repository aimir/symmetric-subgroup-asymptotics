import SymmetricSubgroupAsymptotics.PrimitiveSocleMinimumDegree
import SymmetricSubgroupAsymptotics.PrimitiveSocleExceptionalClassBound
import SymmetricSubgroupAsymptotics.CFSGExceptionalHeisenbergIndex

/-! The same actual prime-field Heisenberg subgroup excludes every bounded
primitive E6/E7/E8 action. The large-degree class bounds consequently apply
at every degree, without a finite list of small fields or actions. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

private theorem degree_lower_of_model_indices {T : Type} [Group T]
    (D : NonaffineData G X) (e : D.Simple ≃* T) (n : ℕ)
    (hindex : ∀ H : Subgroup T, H ≠ ⊤ → n ≤ H.index) : n ≤ Nat.card X := by
  apply D.degree_lower_of_proper_index_lower n
  intro H hH
  have hm : H.map e.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hH
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
  have h := hindex (H.map e.toMonoidHom) hm
  have hi : (H.map e.toMonoidHom).index = H.index := H.index_map_equiv e
  rwa [hi] at h

theorem NonaffineData.e6_degree_ge_2048
    (D : NonaffineData G X) (q : CFSG.PrimePower) (e : D.Simple ≃* CFSG.Models.E6 q) :
    2048 ≤ Nat.card X := by
  letI : IsSimpleGroup (CFSG.Models.E6 q) := e.symm.isSimpleGroup
  exact degree_lower_of_model_indices D e 2048 (typeE6_2048_le_index q)

theorem NonaffineData.e7_degree_ge_2048
    (D : NonaffineData G X) (q : CFSG.PrimePower) (e : D.Simple ≃* CFSG.Models.E7 q) :
    2048 ≤ Nat.card X := by
  letI : IsSimpleGroup (CFSG.Models.E7 q) := e.symm.isSimpleGroup
  exact degree_lower_of_model_indices D e 2048 (typeE7_2048_le_index q)

theorem NonaffineData.e8_degree_ge_2048
    (D : NonaffineData G X) (q : CFSG.PrimePower) (e : D.Simple ≃* CFSG.Models.E8 q) :
    2048 ≤ Nat.card X := by
  letI : IsSimpleGroup (CFSG.Models.E8 q) := e.symm.isSimpleGroup
  exact degree_lower_of_model_indices D e 2048 (typeE8_2048_le_index q)

theorem NonaffineData.subgroup_class_cube_le_of_typeE6_allDegrees
    (D : NonaffineData G X) (q : CFSG.PrimePower) (e : D.Simple ≃* CFSG.Models.E6 q)
    (H : Subgroup G) : Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card X - 1) :=
  D.subgroup_class_cube_le_of_typeE6 q e (by have h := D.e6_degree_ge_2048 q e; omega) H

theorem NonaffineData.subgroup_class_cube_le_of_typeE7_allDegrees
    (D : NonaffineData G X) (q : CFSG.PrimePower) (e : D.Simple ≃* CFSG.Models.E7 q)
    (H : Subgroup G) : Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card X - 1) :=
  D.subgroup_class_cube_le_of_typeE7 q e (by have h := D.e7_degree_ge_2048 q e; omega) H

theorem NonaffineData.subgroup_class_cube_le_of_typeE8_allDegrees
    (D : NonaffineData G X) (q : CFSG.PrimePower) (e : D.Simple ≃* CFSG.Models.E8 q)
    (H : Subgroup G) : Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card X - 1) :=
  D.subgroup_class_cube_le_of_typeE8 q e (by have h := D.e8_degree_ge_2048 q e; omega) H

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
