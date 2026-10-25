import SymmetricSubgroupAsymptotics.LargeTopLieSmallFibreClassBound

/-! A pure order residual for an original large primitive action.
Affine and both raw socle degree forms retain the same group and
point set. All Lie-type component budgets are discharged before
returning literal alternating/Tits/sporadic proper-index data. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveLargeOrderFiniteResidual
open PrimitiveSocleRawStructure CFSGModelComponentIndexOrderBudget

theorem card_le_or_actual_remaining_model (hCFSG : CFSG.CFSGClassification)
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPreprimitive G X]
    (hn : 4096 ≤ Nat.card X) :
    Nat.card G ≤ Nat.card X ^ (4 * Nat.log 2 (Nat.card X) + 30) ∨
      ∃ D : NonaffineData G X, ∃ i : CFSG.Index,
        RemainingSimpleType i ∧ Nonempty (D.Simple ≃* i.Model) ∧
          ∃ K : Subgroup D.Simple, K ≠ ⊤ ∧ Nat.card X = K.index ^ D.factorCount ∧
            K.index ^ (4 * Nat.log 2 K.index + 23) <
              Nat.card D.Simple * Nat.card (Outer D.Simple) ∧
            K.index ^ 66 < Nat.card D.Simple * Nat.card (Outer D.Simple) := by
  letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hpos : 0 < Nat.card X := by omega
  have hlogn : 12 ≤ Nat.log 2 (Nat.card X) :=
    Nat.le_log_of_pow_le (by decide)
      (show 2 ^ 12 ≤ Nat.card X by
        simpa only [show (2 : ℕ) ^ 12 = 4096 by decide] using hn)
  obtain ⟨P⟩ := publishedONanScottStructure G X
  cases P with
  | inr P =>
    left
    calc
      Nat.card G ≤ Nat.card X * Nat.card X ^ Nat.log 2 (Nat.card X) :=
        P.card_le_domain_pow_log (Classical.choice inferInstance)
      _ = Nat.card X ^ (Nat.log 2 (Nat.card X) + 1) := by rw [pow_succ,Nat.mul_comm]
      _ ≤ Nat.card X ^ (4 * Nat.log 2 (Nat.card X) + 30) :=
        Nat.pow_le_pow_right hpos (by omega)
  | inl D =>
    rcases D.indexForm with ⟨K,hK,hdegree⟩ | ⟨a,hka,hdegree⟩
    · by_cases hlog : Nat.card D.Simple * Nat.card (Outer D.Simple) ≤
          K.index ^ (4 * Nat.log 2 K.index + 23)
      · exact Or.inl ((D.card_le_log_order_of_index_form K hK hdegree hlog).trans
          (Nat.pow_le_pow_right hpos (by omega)))
      · by_cases hbound : Nat.card D.Simple * Nat.card (Outer D.Simple) ≤ K.index ^ 66
        · exact Or.inl ((D.card_le_degree_pow_bounded_component K hK hdegree hbound).trans
            (Nat.pow_le_pow_right hpos (by omega)))
        · rcases simple_budget_or_actual_remaining_model hCFSG D.Simple D.noncommutative with
            hbudget | ⟨i,hi,he⟩
          · rcases hbudget K hK with h | h
            · exact (hlog h).elim
            · exact (hbound h).elim
          · exact Or.inr ⟨D,i,hi,he,K,hK,hdegree,lt_of_not_ge hlog,lt_of_not_ge hbound⟩
    · exact Or.inl ((D.card_le_degree_pow_log_of_power_form a hka hdegree (by omega)).trans
        (Nat.pow_le_pow_right hpos (by omega)))

end SymmetricSubgroupAsymptotics.PrimitiveLargeOrderFiniteResidual
