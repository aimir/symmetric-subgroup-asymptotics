import SymmetricSubgroupAsymptotics.UniqueMinimalNormalAbelianLength

/-! A genuine nonabelian chief interval pays its full order charge.
This argument does not require a unique minimal normal subgroup and so
also applies in the presence of central abelian direct factors. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics

variable {G : Type} [Group G] [Finite G]

theorem actualChiefSeriesAbelianLength_add_nonabelian_order_le
    (s : ActualChiefSeries G) (j : Fin s.length)
    (hn : ¬ IsMulCommutative
      (normalChainQuotient (s.subgroup j.castSucc) (s.subgroup j.succ))) :
    actualChiefSeriesAbelianLength s + ArithmeticFunction.cardFactors
      (Nat.card (normalChainQuotient (s.subgroup j.castSucc) (s.subgroup j.succ))) ≤
      ArithmeticFunction.cardFactors (Nat.card G) := by
  have hc (i : Fin s.length) :
      Nat.card (normalChainQuotient (s.subgroup i.castSucc) (s.subgroup i.succ)) =
        (s.subgroup i.castSucc).relIndex (s.subgroup i.succ) := by
    have h := Subgroup.relIndex_ker (s.subgroup i.succ)
      (QuotientGroup.mk' (s.subgroup i.castSucc))
    simpa only [QuotientGroup.ker_mk', normalChainQuotient] using h.symm
  have hp (i : Fin s.length) :
      chiefAbelianLength (normalChainQuotient (s.subgroup i.castSucc) (s.subgroup i.succ)) +
          (if i = j then ArithmeticFunction.cardFactors
            (Nat.card (normalChainQuotient (s.subgroup j.castSucc) (s.subgroup j.succ))) else 0) ≤
        ArithmeticFunction.cardFactors ((s.subgroup i.castSucc).relIndex (s.subgroup i.succ)) := by
    by_cases hi : i = j
    · subst i
      rw [chiefAbelianLength_nonabelian _ hn, if_pos rfl, zero_add, hc]
    · rw [if_neg hi, add_zero]
      unfold chiefAbelianLength
      split
      · exact (congrArg ArithmeticFunction.cardFactors (hc i)).le
      · exact Nat.zero_le _
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin s.length))) => hp i)
  rw [Finset.sum_add_distrib] at hsum
  simp only [actualChiefSeriesAbelianLength, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hsum ⊢
  apply hsum.trans
  have htel := subgroupSeries_cardFactors_sum s.length s.subgroup
    (Fin.strictMono_iff_lt_succ.mpr s.step).monotone
  rw [s.head, s.last, Subgroup.relIndex_top_right, Subgroup.index_bot] at htel
  exact htel.le

end SymmetricSubgroupAsymptotics
