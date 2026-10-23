import SymmetricSubgroupAsymptotics.PrimitiveSoclePowerDegreeOrderBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawONanScottProof
import SymmetricSubgroupAsymptotics.AffineProfileSubgroupClassBound

/-! The actual primitive GM tail reduces to the original first
O'Nan--Scott index form. The affine and entire power-degree forms are
proved here from their existing actual structure, for ALL subgroups of
the original primitive group. The remaining index form is an explicit
residual, not a supplied class or order theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveClassIndexFormReduction
open PrimitiveSocleRawStructure

theorem primitive_all_subgroups_or_actual_index_form
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]
    (hn : 1024 ≤ Nat.card X) :
    (∀ H : Subgroup G, Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1)) ∨
      ∃ D : NonaffineData G X, ∃ K : Subgroup D.Simple,
        K ≠ ⊤ ∧ Nat.card X=K.index^D.factorCount := by
  obtain ⟨D⟩ := publishedONanScottStructure G X
  cases D with
  | inl D =>
    rcases D.indexForm with hindex | ⟨a, hka, hdegree⟩
    · exact Or.inr ⟨D, hindex⟩
    · exact Or.inl (fun H => D.subgroup_class_cube_le_of_power_form a hka hdegree hn H)
  | inr P =>
    let x : X := Classical.choice inferInstance
    exact Or.inl (fun H => AffineProfileSubgroupClassBound.subgroup_class_cube_le_garonziMaroti
      P x (by omega) H)

theorem primitive_subgroup_class_cube_or_actual_index_form
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]
    (hn : 1024 ≤ Nat.card X) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) ∨
      ∃ D : NonaffineData G X, ∃ K : Subgroup D.Simple,
        K ≠ ⊤ ∧ Nat.card X=K.index^D.factorCount := by
  rcases primitive_all_subgroups_or_actual_index_form G X hn with hbound | hindex
  · exact Or.inl (hbound H)
  · exact Or.inr hindex

end SymmetricSubgroupAsymptotics.PrimitiveClassIndexFormReduction
