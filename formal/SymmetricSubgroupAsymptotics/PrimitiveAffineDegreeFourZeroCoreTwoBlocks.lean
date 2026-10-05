import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourZeroCoreExhaustion

/-!
# The impossible two-block zero-core frame

The zero-core quotient embeds faithfully in the action on its actual blocks.
On the other hand, every local coordinate is the exact `C3` or `S3`
complement, so the quotient has order at least three.  Two blocks would
embed that quotient in `S2`, a contradiction.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- A vanishing ternary core is incompatible with exactly two blocks. -/
theorem degreeFourZeroCore_twoBlocks_impossible
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (hs : Nat.card block.Points = 2) : False := by
  let i : block.Points := Classical.choice
    (Finite.card_pos_iff.mp (by rw [hs]; norm_num))
  have hcoord : Function.Surjective
      (fun a : DegreeFourComplementQuotient block P ↦
        (quotientEmbedding block P a).left i) := by
    intro d
    obtain ⟨a, _hai, had⟩ := degreeFourQuotient_fullComponent block P i d
    exact ⟨a, had⟩
  have hlocal : Nat.card (LocalQuotient block P) = 3 ∨
      Nat.card (LocalQuotient block P) = 6 := by
    have hcard : Nat.card (LocalQuotient block P) =
        Nat.card (P.complement (origin block)) :=
      Nat.card_congr (degreeFiveLocalComplementEquiv block P).symm.toEquiv
    simpa only [hcard] using degreeFour_complement_card_eq_three_or_six block P hr
  have hlow : Nat.card (LocalQuotient block P) ≤
      Nat.card (DegreeFourComplementQuotient block P) :=
    Nat.card_le_card_of_surjective _ hcoord
  have hthree : 3 ≤ Nat.card (DegreeFourComplementQuotient block P) := by
    rcases hlocal with h3 | h6 <;> omega
  have hhigh := Nat.card_le_card_of_injective
    (degreeFourZeroCoreTopAction block P)
    (degreeFourZeroCoreTopAction_injective block P hr hD)
  have hperm : Nat.card (Equiv.Perm (Fin (Nat.card block.Points))) = 2 := by
    rw [hs]
    rw [Nat.card_perm, Nat.card_fin]
    norm_num
  rw [hperm] at hhigh
  omega

/-- Source wrapper for the impossible two-block residue. -/
noncomputable def degreeFourZeroCoreTwoBlockSource
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (hs : Nat.card block.Points = 2) :
    PreE7RankTailSourceOrYonedaTopData w U :=
  False.elim (degreeFourZeroCore_twoBlocks_impossible block P hr hD hs)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
