import SymmetricSubgroupAsymptotics.ActualWreathChooseDivisorCapacity
import SymmetricSubgroupAsymptotics.ActualWreathChiefLayerWeightBudget

/-! Exact choose-on-divisor weights on the SAME actual finite chief
trace. Elementary layers use their literal induced representations;
nonabelian layers retain the proved internal-factor ordinary rank cost.
No equality between the index and the chosen primary divisor is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualWreathChiefChooseDivisorWeights
open ActualWreathChooseDivisorCapacity ActualWreathChiefWeightedPrimeBudget

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
    [MulAction Q I] [FaithfulSMul Q I]

theorem layerCapacity_le_min_divisorWeights (S : ActualWreathCompressionState Q I)
    {D' : Type} [Group D'] (phi : S.D →* D')
    (C : ElementaryMinimalNormalChart phi.ker) (i : I) (hI : 2 ≤ Fintype.card I)
    (q e r f : ℕ) (hq : q.Prime) (hqd : q^e ∣ Fintype.card I)
    (hr : r.Prime) (hrd : r^f ∣ Fintype.card I) :
    (ActualWreathElementaryOrdinaryStep.layerCapacity S phi C i : ℝ) ≤
      (Module.finrank (ZMod C.p) C.V : ℝ)*
        min (divisorWeight (Fintype.card I) q e C.p)
          (divisorWeight (Fintype.card I) r f C.p) := by
  rw [mul_min_of_nonneg _ _ (show (0 : ℝ) ≤ Module.finrank (ZMod C.p) C.V by positivity)]
  exact le_min (layerCapacity_le_divisorWeight S phi C i hI q e hq hqd)
    (layerCapacity_le_divisorWeight S phi C i hI r f hr hrd)

theorem cost_le_divisorWeight {i : I} {S : ActualWreathCompressionState Q I} {n : ℕ}
    (h : ActualWreathOrdinaryChiefRecurrence.ChiefCost i S n)
    (hI : 2 ≤ Fintype.card I) (q e : ℕ) (hq : q.Prime)
    (hd : q^e ∣ Fintype.card I) :
    (n : ℝ) ≤ weightedOrder (divisorWeight (Fintype.card I) q e) (Nat.card S.D) := by
  apply ActualWreathChiefLayerWeightBudget.cost_le_weightedOrder h _
    (one_le_divisorWeight _ q e)
  intro T D' _ _ phi C
  exact layerCapacity_le_divisorWeight T phi C i hI q e hq hd

theorem cost_le_min_divisorWeights {i : I} {S : ActualWreathCompressionState Q I} {n : ℕ}
    (h : ActualWreathOrdinaryChiefRecurrence.ChiefCost i S n)
    (hI : 2 ≤ Fintype.card I) (q e r f : ℕ)
    (hq : q.Prime) (hqd : q^e ∣ Fintype.card I)
    (hr : r.Prime) (hrd : r^f ∣ Fintype.card I) :
    (n : ℝ) ≤ weightedOrder
      (fun p => min (divisorWeight (Fintype.card I) q e p)
        (divisorWeight (Fintype.card I) r f p)) (Nat.card S.D) := by
  apply ActualWreathChiefLayerWeightBudget.cost_le_weightedOrder h _
  · intro p
    exact le_min (one_le_divisorWeight _ q e p) (one_le_divisorWeight _ r f p)
  · intro T D' _ _ phi C
    exact layerCapacity_le_min_divisorWeights T phi C i hI q e r f hq hqd hr hrd

theorem exists_divisorWeight_bound (S : ActualWreathCompressionState Q I)
    (i : I) (hI : 2 ≤ Fintype.card I) (q e : ℕ) (hq : q.Prime)
    (hd : q^e ∣ Fintype.card I) :
    ∃ n : ℕ, ActualWreathOrdinaryChiefRecurrence.ChiefCost i S n ∧
      (n : ℝ) ≤ weightedOrder (divisorWeight (Fintype.card I) q e) (Nat.card S.D) ∧
      MarkedC4.genRank S.A ≤ n + MarkedC4.genRank Q := by
  obtain ⟨n,hn⟩ := ActualWreathOrdinaryChiefRecurrence.exists_chiefCost i S
  exact ⟨n,hn,cost_le_divisorWeight hn hI q e hq hd,
    ActualWreathOrdinaryChiefRecurrence.genRank_le_cost_add_top hn⟩

end SymmetricSubgroupAsymptotics.ActualWreathChiefChooseDivisorWeights
