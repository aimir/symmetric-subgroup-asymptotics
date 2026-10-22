import SymmetricSubgroupAsymptotics.UniqueMinimalNormalAbelianLength
import SymmetricSubgroupAsymptotics.FixedTargetCompositionTrace

/-! An original chief trace spends at least one prime-factor unit on every
nonabelian interval. This is a genuine order bound, not a composition-length
assumption, and retains the whole chosen series. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGChiefPrimeFactorBudget

variable {G : Type} [Group G] [Finite G]

theorem interval_charge_le_cardFactors :
    chiefAbelianLength G + chiefNonabelianIndicator G ≤
      ArithmeticFunction.cardFactors (Nat.card G) := by
  by_cases hc : IsMulCommutative G
  · simp only [chiefAbelianLength,chiefNonabelianIndicator,if_pos hc,add_zero]
    exact le_rfl
  · have hn : ¬ Subsingleton G := by
      intro hs
      letI : Subsingleton G := hs
      exact hc ⟨⟨fun _ _ => Subsingleton.elim _ _⟩⟩
    letI : Nontrivial G := not_subsingleton_iff_nontrivial.mp hn
    simp only [chiefAbelianLength,chiefNonabelianIndicator,if_neg hc,zero_add]
    exact (ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr
      (Finite.one_lt_card (α := G)))

theorem original_chief_charge_le_cardFactors (c : ActualChiefSeries G) :
    actualChiefSeriesAbelianLength c + actualChiefSeriesNonabelianCount c ≤
      ArithmeticFunction.cardFactors (Nat.card G) := by
  have hc (i : Fin c.length) : Nat.card
      (normalChainQuotient (c.subgroup i.castSucc) (c.subgroup i.succ)) =
      (c.subgroup i.castSucc).relIndex (c.subgroup i.succ) := by
    have h := Subgroup.relIndex_ker (c.subgroup i.succ)
      (QuotientGroup.mk' (c.subgroup i.castSucc))
    simpa only [QuotientGroup.ker_mk',normalChainQuotient] using h.symm
  unfold actualChiefSeriesAbelianLength actualChiefSeriesNonabelianCount
  rw [← Finset.sum_add_distrib]
  calc
    _ ≤ ∑ i : Fin c.length, ArithmeticFunction.cardFactors
        (Nat.card (normalChainQuotient (c.subgroup i.castSucc) (c.subgroup i.succ))) :=
      Finset.sum_le_sum (fun i _ => interval_charge_le_cardFactors)
    _ = ∑ i : Fin c.length, ArithmeticFunction.cardFactors
        ((c.subgroup i.castSucc).relIndex (c.subgroup i.succ)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hc]
    _ = ArithmeticFunction.cardFactors (Nat.card G) := by
      have htel := subgroupSeries_cardFactors_sum c.length c.subgroup
        (Fin.strictMono_iff_lt_succ.mpr c.step).monotone
      rw [c.head,c.last,Subgroup.relIndex_top_right,Subgroup.index_bot] at htel
      exact htel

theorem trace_charge_le_cardFactors (T : FixedTargetCompositionTrace G) :
    T.envelope.abelianLength + T.nonabelianCount ≤
      ArithmeticFunction.cardFactors (Nat.card G) := by
  rw [T.abelianLength_eq,T.nonabelianCount_eq]
  exact original_chief_charge_le_cardFactors T.chief

theorem trace_nonsoluble_saving (T : FixedTargetCompositionTrace G)
    (hn : ¬ IsSolvable G) : T.envelope.abelianLength+1 ≤
      ArithmeticFunction.cardFactors (Nat.card G) := by
  have h := trace_charge_le_cardFactors T
  have hp := T.one_le_nonabelianCount_of_not_solvable hn
  omega

theorem cardFactors_mono {a b : ℕ} (hb : b ≠ 0) (h : a ∣ b) :
    ArithmeticFunction.cardFactors a ≤ ArithmeticFunction.cardFactors b := by
  obtain ⟨k,rfl⟩ := h
  have ha : a ≠ 0 := left_ne_zero_of_mul hb
  have hk : k ≠ 0 := right_ne_zero_of_mul hb
  rw [ArithmeticFunction.cardFactors_mul ha hk]
  omega

end SymmetricSubgroupAsymptotics.CFSGChiefPrimeFactorBudget
