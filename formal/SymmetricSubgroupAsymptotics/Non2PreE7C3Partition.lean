import SymmetricSubgroupAsymptotics.Non2PreE7ResidualPairPartition
import SymmetricSubgroupAsymptotics.C3HighAlignedRefinedExhaustion

/-!
# Remove the closed regular-C3 sector from the pre-E7 frontier

The complete regular-`C3` physical family already has a closed forward
estimate.  This file transports that family to every ambient `Fin n`, cuts it
out of the exact non-pair pre-`E7` residual, and leaves one still smaller
complement.  The paid family and the complement are literal subtype pieces,
so this introduces neither a pointing multiplicity nor overlapping ownership.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- The canonical point equivalence identifying `3 + (n - 3)` with `n`. -/
def c3AmbientPointEquiv (n : ℕ) (hn : 3 ≤ n) :
    Fin (3 + (n - 3)) ≃ Fin n :=
  finCongr (Nat.add_sub_of_le hn)

/-- The already counted complete regular-`C3` family, transported to the
literal ambient point type `Fin n`. -/
def C3CompleteOrdinaryPhysicalAt (n : ℕ) :
    Set (Subgroup (Equiv.Perm (Fin n))) :=
  if hn : 3 ≤ n then
    {G | relabelSubgroup (c3AmbientPointEquiv n hn).symm G ∈
      C3CompleteOrdinaryPhysicalSet (n - 3)}
  else ∅

private def c3CompleteOrdinaryPhysicalAtEquiv (n : ℕ) (hn : 3 ≤ n) :
    C3CompleteOrdinaryPhysicalSet (n - 3) ≃
      C3CompleteOrdinaryPhysicalAt n where
  toFun G := ⟨relabelSubgroup (c3AmbientPointEquiv n hn) G.1, by
    simp only [C3CompleteOrdinaryPhysicalAt, dif_pos hn, Set.mem_setOf_eq]
    simpa only [relabelSubgroup_symm] using G.2⟩
  invFun G := ⟨relabelSubgroup (c3AmbientPointEquiv n hn).symm G.1, by
    simpa only [C3CompleteOrdinaryPhysicalAt, dif_pos hn, Set.mem_setOf_eq]
      using G.2⟩
  left_inv G := by
    apply Subtype.ext
    exact relabelSubgroup_symm (c3AmbientPointEquiv n hn) G.1
  right_inv G := by
    apply Subtype.ext
    simpa only using relabelSubgroup_symm
      (c3AmbientPointEquiv n hn).symm G.1

theorem c3CompleteOrdinaryPhysicalAt_card (n : ℕ) (hn : 3 ≤ n) :
    Nat.card (C3CompleteOrdinaryPhysicalAt n) =
      Nat.card (C3CompleteOrdinaryPhysicalSet (n - 3)) :=
  Nat.card_congr (c3CompleteOrdinaryPhysicalAtEquiv n hn).symm

/-- The transported physical family has exactly the previously proved
regular-`C3` normalized ratio. -/
theorem c3CompleteOrdinaryPhysicalAt_ratio (n : ℕ) :
    (Nat.card (C3CompleteOrdinaryPhysicalAt n) : ℝ) / exactBenchmark n =
      c3CompleteOrdinaryRatio n := by
  by_cases hn : 3 ≤ n
  · unfold c3CompleteOrdinaryRatio
    rw [if_pos hn, c3CompleteOrdinaryPhysicalAt_card n hn]
  · have hempty : C3CompleteOrdinaryPhysicalAt n = ∅ := by
      simp only [C3CompleteOrdinaryPhysicalAt, dif_neg hn]
    unfold c3CompleteOrdinaryRatio
    rw [if_neg hn, hempty]
    simp

/-- The part of the exact non-pair residual already lying in the closed
regular-`C3` physical family. -/
abbrev PreE7C3CoveredFamily (n : ℕ) :=
  {H : PreE7NonPairResidualFamily n //
    H.1.1.1 ∈ C3CompleteOrdinaryPhysicalAt n}

/-- The remaining pre-`E7` family after both pair menus and the complete
regular-`C3` family have been removed. -/
abbrev PreE7NoPairNoC3ResidualFamily (n : ℕ) :=
  {H : PreE7NonPairResidualFamily n //
    H.1.1.1 ∉ C3CompleteOrdinaryPhysicalAt n}

def preE7C3PartitionEquiv (n : ℕ) :
    PreE7NonPairResidualFamily n ≃
      PreE7C3CoveredFamily n ⊕ PreE7NoPairNoC3ResidualFamily n :=
  (Equiv.sumCompl
    (fun H : PreE7NonPairResidualFamily n =>
      H.1.1.1 ∈ C3CompleteOrdinaryPhysicalAt n)).symm

def preE7C3CoveredRatio (n : ℕ) : ℝ :=
  (Nat.card (PreE7C3CoveredFamily n) : ℝ) / exactBenchmark n

def preE7NoPairNoC3ResidualRatio (n : ℕ) : ℝ :=
  (Nat.card (PreE7NoPairNoC3ResidualFamily n) : ℝ) / exactBenchmark n

theorem preE7NonPairResidualRatio_eq_c3_partition (n : ℕ) :
    preE7NonPairResidualRatio n =
      preE7C3CoveredRatio n + preE7NoPairNoC3ResidualRatio n := by
  have hcard : Nat.card (PreE7NonPairResidualFamily n) =
      Nat.card (PreE7C3CoveredFamily n) +
        Nat.card (PreE7NoPairNoC3ResidualFamily n) := by
    rw [Nat.card_congr (preE7C3PartitionEquiv n), Nat.card_sum]
  unfold preE7NonPairResidualRatio preE7C3CoveredRatio
    preE7NoPairNoC3ResidualRatio
  rw [hcard, Nat.cast_add, add_div]

def preE7C3CoveredEmbedding (n : ℕ) :
    PreE7C3CoveredFamily n ↪ C3CompleteOrdinaryPhysicalAt n where
  toFun H := ⟨H.1.1.1.1, H.2⟩
  inj' := by
    intro H K h
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg
      (fun G : C3CompleteOrdinaryPhysicalAt n => G.1) h

theorem preE7C3CoveredRatio_le_c3 (n : ℕ) :
    preE7C3CoveredRatio n ≤ c3CompleteOrdinaryRatio n := by
  have hcard : Nat.card (PreE7C3CoveredFamily n) ≤
      Nat.card (C3CompleteOrdinaryPhysicalAt n) :=
    Nat.card_le_card_of_injective
      (preE7C3CoveredEmbedding n) (preE7C3CoveredEmbedding n).injective
  rw [← c3CompleteOrdinaryPhysicalAt_ratio n]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hcard)
    (exactBenchmark_pos n).le

/-- The covered side inherits the fully assembled regular-`C3` estimate. -/
noncomputable def preE7C3Covered_exponentialForwardEstimate
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      preE7C3CoveredRatio :=
  OrdinaryFrontierClosure.ExponentialForwardEstimate.of_le
    (c3CompleteOrdinary_closedExponentialForwardEstimate
      hChief hWeight hPrimitive h18 hKP) 0
    (fun n _ => preE7C3CoveredRatio_le_c3 n)

/-- A forward estimate for the exact complement after the regular-`C3` cut
closes the whole non-pair pre-`E7` residual. -/
noncomputable def preE7NonPair_exponentialForwardEstimate_of_noC3
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (P : OrdinaryFrontierClosure.ExponentialForwardEstimate
      preE7NoPairNoC3ResidualRatio) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      preE7NonPairResidualRatio := by
  let E := OrdinaryFrontierClosure.ExponentialForwardEstimate.add
    (preE7C3Covered_exponentialForwardEstimate
      hChief hWeight hPrimitive h18 hKP) P
  exact OrdinaryFrontierClosure.ExponentialForwardEstimate.of_le E 0
    (fun n _ => by rw [preE7NonPairResidualRatio_eq_c3_partition])

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
