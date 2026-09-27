import SymmetricSubgroupAsymptotics.OddZeroDefectCoverage

/-!
# Complete intrinsic repeated-marker owner bounds

The literal `Fits` owner inside the ordinary remainder splits exhaustively
into positive and zero orbit defect.  The positive branch uses the checked
strictly forward marker row.  The even zero branch enters the intrinsic
binary error unchanged; the odd zero branch uses the exhaustive singleton/
natural-marker coverage theorem.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.RepeatedMarkerOwnerBound

abbrev OrdinaryFullFamily (N epsilon : ℕ) :=
  RepeatedMarkerZeroDefect.FullFamily N epsilon
    (fun H => ¬ IsCriticalSubgroup (2*N+epsilon) H)

abbrev OrdinaryPositiveFamily (N epsilon : ℕ) :=
  RepeatedMarkerIntrinsicPositive.Family N epsilon
    (fun H => ¬ IsCriticalSubgroup (2*N+epsilon) H)

abbrev OrdinaryZeroFamily (N epsilon : ℕ) :=
  RepeatedMarkerZeroDefect.Family N epsilon
    (fun H => ¬ IsCriticalSubgroup (2*N+epsilon) H)

abbrev OutsideFitsFamily (N epsilon : ℕ) :=
  {H : OrdinaryRemainderSubgroups (2*N+epsilon) //
    ¬ RepeatedMarkerOrbitProfiles.Fits H.1}

local instance ordinaryFullFamilyFinite (N epsilon : ℕ) :
    Finite (OrdinaryFullFamily N epsilon) :=
  Finite.of_injective
    (fun H : OrdinaryFullFamily N epsilon =>
      (H.1 : Set (Equiv.Perm (Fin (2*N+epsilon)))))
    (fun _ _ h => Subtype.ext (SetLike.coe_injective h))

def fitsRemainderEquiv (N epsilon : ℕ) :
    {H : OrdinaryRemainderSubgroups (2*N+epsilon) //
      RepeatedMarkerOrbitProfiles.Fits H.1} ≃ OrdinaryFullFamily N epsilon where
  toFun H := ⟨H.1.1,H.2,H.1.2⟩
  invFun H := ⟨⟨H.1,H.2.2⟩,H.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact frontier after completing the repeated-marker owner: the only
remaining ordinary subgroups are those having a literal orbit image outside
the binary/full-S3 alphabet. -/
def ordinaryRemainderPartitionEquiv (N epsilon : ℕ) :
    OrdinaryRemainderSubgroups (2*N+epsilon) ≃
      OrdinaryFullFamily N epsilon ⊕ OutsideFitsFamily N epsilon :=
  (Equiv.sumCompl (fun H : OrdinaryRemainderSubgroups (2*N+epsilon) =>
    RepeatedMarkerOrbitProfiles.Fits H.1)).symm |>.trans
      (Equiv.sumCongr (fitsRemainderEquiv N epsilon) (Equiv.refl _))

theorem ordinaryRemainder_card_partition (N epsilon : ℕ) :
    Nat.card (OrdinaryRemainderSubgroups (2*N+epsilon)) =
      Nat.card (OrdinaryFullFamily N epsilon) +
        Nat.card (OutsideFitsFamily N epsilon) := by
  rw [Nat.card_congr (ordinaryRemainderPartitionEquiv N epsilon),Nat.card_sum]

def outsideFitsRatio (N epsilon : ℕ) : ℝ :=
  (Nat.card (OutsideFitsFamily N epsilon) : ℝ) /
    exactBenchmark (2*N+epsilon)

theorem ordinaryRemainderRatio_partition (N epsilon : ℕ) :
    ordinaryRemainderRatio (2*N+epsilon) =
      (Nat.card (OrdinaryFullFamily N epsilon) : ℝ) /
        exactBenchmark (2*N+epsilon) + outsideFitsRatio N epsilon := by
  unfold ordinaryRemainderRatio outsideFitsRatio
  rw [ordinaryRemainder_card_partition,Nat.cast_add,add_div]

theorem even_zero_normalized_le (N : ℕ) :
    (Nat.card (OrdinaryZeroFamily N 0) : ℝ) / exactBenchmark (2*N) ≤
      binaryErrorRatio N := by
  unfold binaryErrorRatio
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast RepeatedMarkerZeroDefect.even_card_le_noncriticalBinary N)
    (exactBenchmark_pos _).le

/-- Exhaustive even repeated-marker owner: a strictly forward positive row
plus the unchanged intrinsic binary error. -/
theorem even_normalized_le (N : ℕ) :
    (Nat.card (OrdinaryFullFamily N 0) : ℝ) / exactBenchmark (2*N) ≤
      (∑ m ∈ Finset.range (2*N),
        MarkerDegreeForwardRow.kernel (2*N) m * ordinarySubgroupRatio m) +
        binaryErrorRatio N := by
  rw [RepeatedMarkerZeroDefect.card_partition,Nat.cast_add,add_div]
  exact add_le_add
    (RepeatedMarkerIntrinsicPositive.positive_card_div_benchmark_le
      N 0 (by omega) (fun H => ¬ IsCriticalSubgroup (2*N) H))
    (even_zero_normalized_le N)

/-- Exhaustive odd repeated-marker owner: the same strictly forward row
plus the checked current/predecessor binary-error transfer. -/
theorem odd_normalized_le (N : ℕ) (hN : 1 ≤ N) :
    (Nat.card (OrdinaryFullFamily N 1) : ℝ) / exactBenchmark (2*N+1) ≤
      (∑ m ∈ Finset.range (2*N+1),
        MarkerDegreeForwardRow.kernel (2*N+1) m * ordinarySubgroupRatio m) +
        (OddMarkerBinaryErrorTransfer.currentCoefficient N * binaryErrorRatio N +
          OddMarkerBinaryErrorTransfer.predecessorErrorCoefficient N *
            binaryErrorRatio (N-1)) := by
  rw [RepeatedMarkerZeroDefect.card_partition,Nat.cast_add,add_div]
  exact add_le_add
    (RepeatedMarkerIntrinsicPositive.positive_card_div_benchmark_le
      N 1 (by omega) (fun H => ¬ IsCriticalSubgroup (2*N+1) H))
    (OddZeroDefectCoverage.normalized_card_le N hN)

theorem even_remainder_frontier (N : ℕ) :
    ordinaryRemainderRatio (2*N) ≤
      outsideFitsRatio N 0 +
        (∑ m ∈ Finset.range (2*N),
          MarkerDegreeForwardRow.kernel (2*N) m * ordinarySubgroupRatio m) +
        binaryErrorRatio N := by
  have hp := ordinaryRemainderRatio_partition N 0
  simp only [Nat.add_zero] at hp
  rw [hp]
  linarith [even_normalized_le N]

theorem odd_remainder_frontier (N : ℕ) (hN : 1 ≤ N) :
    ordinaryRemainderRatio (2*N+1) ≤
      outsideFitsRatio N 1 +
        (∑ m ∈ Finset.range (2*N+1),
          MarkerDegreeForwardRow.kernel (2*N+1) m * ordinarySubgroupRatio m) +
        (OddMarkerBinaryErrorTransfer.currentCoefficient N * binaryErrorRatio N +
          OddMarkerBinaryErrorTransfer.predecessorErrorCoefficient N *
            binaryErrorRatio (N-1)) := by
  rw [ordinaryRemainderRatio_partition N 1]
  linarith [odd_normalized_le N hN]

end SymmetricSubgroupAsymptotics.RepeatedMarkerOwnerBound

end
