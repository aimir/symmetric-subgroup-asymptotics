import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveCapacityExhaustion
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitivePairFrameExclusion

/-!
# The surviving degree-two affine-frame cells

The numerical degree-two exhaustion leaves powers of two through `256` and
three times powers of two through `3072`.  The literal two-point minimal
block supplies a binary pair frame.  Hence the eight selected pair counts
and four residual pair counts are impossible in the non-pair action index.
After also using the ambient lower bound `5 ≤ w`, exactly six block counts
remain: `3, 4, 6, 8, 12, 16`.

This is a structural reduction only.  The six surviving cells still have to
be sent to their already integrated small-pair owners.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace ComponentSource

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)

/-- Every degree-two numerical exception which survives the literal pair
exclusions has one of the six genuinely small block counts. -/
theorem degreeTwoException_small
    (hw : 5 ≤ w)
    (hr : Nat.card block.Fibre = 2)
    (h : IsDegreeTwoAffineExceptionalBlockCount
      (Nat.card block.Points)) :
    Nat.card block.Points = 3 ∨ Nat.card block.Points = 4 ∨
      Nat.card block.Points = 6 ∨ Nat.card block.Points = 8 ∨
      Nat.card block.Points = 12 ∨ Nat.card block.Points = 16 := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hwidth : 2 * Nat.card block.Points = w := by
    simpa only [hr] using (width_eq block).symm
  have hpoints : 3 ≤ Nat.card block.Points := by omega
  have hsplit :
      (Nat.card block.Points = 3 ∨ Nat.card block.Points = 4 ∨
        Nat.card block.Points = 6 ∨ Nat.card block.Points = 8 ∨
        Nat.card block.Points = 12 ∨ Nat.card block.Points = 16) ∨
      (Nat.card block.Points = 24 ∨ Nat.card block.Points = 32 ∨
        Nat.card block.Points = 48 ∨ Nat.card block.Points = 64 ∨
        Nat.card block.Points = 96 ∨ Nat.card block.Points = 128 ∨
        Nat.card block.Points = 192 ∨ Nat.card block.Points = 256) ∨
      (Nat.card block.Points = 384 ∨ Nat.card block.Points = 768 ∨
        Nat.card block.Points = 1536 ∨ Nat.card block.Points = 3072) := by
    rcases h with ⟨a, ha1, ha8, hs⟩ | ⟨a, ha10, hs⟩
    · interval_cases a <;> norm_num at ha1 ha8 hs <;>
        simp only [Fintype.card_eq_nat_card] at hs
      all_goals omega
    · interval_cases a <;> norm_num at ha10 hs <;>
        simp only [Fintype.card_eq_nat_card] at hs
      all_goals omega
  rcases hsplit with hsmall | hselected | hresidual
  · exact hsmall
  · obtain ⟨d, hd⟩ := PairCountLabel.exists_of_pairCount_menu hselected
    exact False.elim
      ((fibre_card_ne_two_of_selectedPairWidth U block d
        (by unfold PairCountLabel.sourceDegree; rw [hd]; exact hwidth)) hr)
  · rcases hresidual with h384 | h768 | h1536 | h3072
    · exact False.elim
        ((fibre_card_ne_two_of_residualPairWidth U block .c384
          (by simp only [PreE7ResidualPairCountLabel.pairCount]; omega)) hr)
    · exact False.elim
        ((fibre_card_ne_two_of_residualPairWidth U block .c768
          (by simp only [PreE7ResidualPairCountLabel.pairCount]; omega)) hr)
    · exact False.elim
        ((fibre_card_ne_two_of_residualPairWidth U block .c1536
          (by simp only [PreE7ResidualPairCountLabel.pairCount]; omega)) hr)
    · exact False.elim
        ((fibre_card_ne_two_of_residualPairWidth U block .c3072
          (by simp only [PreE7ResidualPairCountLabel.pairCount]; omega)) hr)

end ComponentSource
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
