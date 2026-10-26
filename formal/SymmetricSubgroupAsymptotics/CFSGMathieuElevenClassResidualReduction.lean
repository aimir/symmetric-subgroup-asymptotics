import SymmetricSubgroupAsymptotics.CFSGMathieuElevenCompleteClassConsumers
import SymmetricSubgroupAsymptotics.PrimitiveAllDegreeReeFFourCompleteCFSGReduction
import SymmetricSubgroupAsymptotics.SmallFibreNonaffineFiniteModelNormalization

/-! The SAME actual finite-model residual with only M11 removed. The
primitive action, subnormal subgroup, selected simple factor/equivalence,
both degree forms, and original small-fibre block system remain literal.
No existing exhaustive profile is changed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuElevenClassResidualReduction
open PrimitiveSocleRawStructure

def RemainingFiniteSimpleType (i : CFSG.Index) : Prop :=
  PrimitiveAllDegreeReeFFourCompleteCFSGReduction.RemainingFiniteSimpleType i ∧
    i ≠ .sporadic .m11

theorem primitive_subnormal_cube_or_finite_model
    (hCFSG : CFSG.CFSGClassification)
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]
    (hn : 4 ≤ Nat.card X) (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card X - 1) ∨
      ∃ D : NonaffineData G X, ∃ i : CFSG.Index,
        Nonempty (D.Simple ≃* i.Model) ∧ RemainingFiniteSimpleType i ∧
        ((∃ K : Subgroup D.Simple, K ≠ ⊤ ∧ Nat.card X = K.index ^ D.factorCount) ∨
          (∃ a : ℕ, D.factorCount ≤ 2 * a ∧ Nat.card X = (Nat.card D.Simple) ^ a)) := by
  rcases PrimitiveAllDegreeReeFFourCompleteCFSGReduction.primitive_subnormal_cube_or_finite_model
    hCFSG G X hn H hH with hpaid | ⟨D,i,⟨e⟩,hi,hform⟩
  · exact Or.inl hpaid
  · by_cases hm : i = .sporadic .m11
    · subst i
      exact Or.inl (CFSGMathieuElevenCompleteClassConsumers.primitive_subnormal_class_cube D e H hH)
    · exact Or.inr ⟨D,i,⟨e⟩,⟨hi,hm⟩,hform⟩

theorem original_small_fibre_cube_or_same_selected_model
    {A Ω : Type} [Group A] [MulAction A Ω] [MulAction.IsPretransitive A Ω]
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)
    (hsmall : Nat.card D.Fibre = 2 ∨ Nat.card D.Fibre = 3)
    (hclosed : ¬SmallFibreKnownModelGlobalClassGap.HasClosedTop D)
    (E : NonaffineData D.Top D.Points) (i : CFSG.Index) (e : E.Simple ≃* i.Model) :
    Nat.card (ConjClasses A) ^ 3 ≤ 5 ^ (Nat.card Ω - 1) ∨
      RemainingFiniteSimpleType i := by
  have htag := SmallFibreNonaffineFiniteModelNormalization.original_top_index_is_tits_or_sporadic
    D hclosed E i e
  by_cases hm : i = .sporadic .m11
  · subst i
    have hh := CFSGMathieuElevenCompleteClassConsumers.original_small_fibre_subnormal_gap
      D.map D.map_equivariant (Nat.card D.Fibre) hsmall D.fibre_card_at E e
      (⊤ : Subgroup A) (Subgroup.Normal.isSubnormal inferInstance)
    have he := conjugacyClass_card_congr (Subgroup.topEquiv : (⊤ : Subgroup A) ≃* A)
    rw [he] at hh
    exact Or.inl (hh.trans (Nat.pow_le_pow_right (by decide : 0 < 5) (by omega)))
  · right
    refine ⟨?_,hm⟩
    rcases htag with rfl | ⟨s,rfl⟩ <;>
      trivial

end SymmetricSubgroupAsymptotics.CFSGMathieuElevenClassResidualReduction
