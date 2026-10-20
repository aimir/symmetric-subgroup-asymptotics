import SymmetricSubgroupAsymptotics.MarkedC4ActualHistoryKeyFibre

/-! Global original-word bound from the actual finite key partition.
The whole order/normal-chain menu is charged ONCE, the stopping cost ONCE,
and the single vertical Hall polynomial ONCE. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualGlobalHistoryBound
open ActualExcessHistoryPartition RDTOriginalWordStructure RDTNormalFInterface

/-- Exact global menu cost, before its elementary logarithmic absorption. -/
def menuCost (t K : ℕ) : ℝ := (t.factorial*(t+1)^((2^K)*t) : ℕ)

theorem card_le
    (hKP : KovacsPraegerBinaryAbelianQuotientBound) (h55 : PublishedTheorem55Binary)
    (h53 : ActualCaseIITargetStructure.PublishedProposition53Binary)
    (h57 : RDTExcessStructure.PublishedTheorem57Binary)
    (h8 : RDTDegreeEightExceptional.PublishedDegreeEightExceptional)
    (hderived : RDTDerivedNormalQuarter.PublishedDerivedNormalQuarterBinary)
    (lit : RDTTheorem46BinaryInput)
    {t : ℕ} (n : Fin t → ℕ) (G : ∀ i,Subgroup (Equiv.Perm (Fin (n i))))
    (C B r K : ℕ) (hK : ∀ i,Nat.card (G i)≤K)
    (hpositive : ∀ i,0<n i) (hcut : ∀ i,n i≤C)
    (hG : ∀ i,IsPGroup 2 (G i))
    (htrans : ∀ i,∀ x y : Fin (n i),∃ g : G i,g.val x=y)
    (hB : (∑ i : Fin t,n i)≤B) :
    (Nat.card (ActualFullPhysicalWordPeel.Family (fun i => ↥(G i))
      (ActualGlobalMarkGeneratorRank.Marks r)) : ℝ) ≤
      menuCost t K * ActualFixedHistoryBound.envelope lit C B r t *
        (2 : ℝ)^markedF (∑ i : Fin t,(n i : ℝ)) r := by
  let R : ℝ := ActualFixedHistoryBound.envelope lit C B r t *
    (2 : ℝ)^markedF (∑ i : Fin t,(n i : ℝ)) r
  have hR : 0 ≤ R := by
    unfold R ActualFixedHistoryBound.envelope
    have hp : 0 ≤ VerticalHallBase.polynomial r :=
      (by norm_num : (0 : ℝ) ≤ 1).trans (VerticalHallBase.polynomial_one_le r)
    have hs : 0 ≤ ActualFixedHistoryBound.stoppingCost C B :=
      (by norm_num : (0 : ℝ) ≤ 1).trans (ActualFixedHistoryBound.stoppingCost_one_le C B)
    have hd : 0 ≤ ActualUniformEpiReserve.peelFactor lit C B r :=
      (by norm_num : (0 : ℝ) ≤ 1).trans (ActualFixedHistoryBound.peelFactor_one_le lit C B r)
    exact mul_nonneg (mul_nonneg (mul_nonneg hp hs) (pow_nonneg hd _)) (by positivity)
  have hf : ∀ q : Key n G,
      (Nat.card (Fibre n G (ActualGlobalMarkGeneratorRank.Marks r) q) : ℝ) ≤ R := by
    intro q
    by_cases hh : Nonempty (Fibre n G (ActualGlobalMarkGeneratorRank.Marks r) q)
    · obtain ⟨J⟩ := hh
      exact ActualHistoryKeyFibre.card_le n G r q J hKP h55 h53 h57 h8 hderived lit C B
        hpositive hcut hG htrans hB
    · letI : IsEmpty (Fibre n G (ActualGlobalMarkGeneratorRank.Marks r) q) :=
        not_nonempty_iff.mp hh
      letI : Fintype (Fibre n G (ActualGlobalMarkGeneratorRank.Marks r) q) := Fintype.ofFinite _
      have hz : Nat.card (Fibre n G (ActualGlobalMarkGeneratorRank.Marks r) q)=0 := by
        simp [Nat.card_eq_fintype_card]
      simpa only [hz,Nat.cast_zero] using hR
  have hpartition := card_eq_sum n G (ActualGlobalMarkGeneratorRank.Marks r)
  have hs : (Nat.card (ActualFullPhysicalWordPeel.Family (fun i => ↥(G i))
      (ActualGlobalMarkGeneratorRank.Marks r)) : ℝ) ≤ (Nat.card (Key n G) : ℝ)*R := by
    rw [hpartition,Nat.cast_sum]
    calc
      _ ≤ ∑ q : Key n G,R := Finset.sum_le_sum (fun q _ => hf q)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
  have hk : (Nat.card (Key n G) : ℝ) ≤ menuCost t K := by
    unfold menuCost
    exact_mod_cast card_key_le n G K hK
  simpa only [R,mul_assoc] using hs.trans (mul_le_mul_of_nonneg_right hk hR)

end SymmetricSubgroupAsymptotics.MarkedC4.ActualGlobalHistoryBound
