import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourOriginalLocalFaithfulness

/-! Transport actual local faithfulness to every original block, so the
fixed and moving fibres of a Sylow normalizer use the same literal local
quotient. Only stabilizers are conjugated; the original local maps remain. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]

theorem originalLocalMap_injective_of_one
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥)
    (i0 : block.Points)
    (hinj : Function.Injective (binaryAffineStabilizerComponent block P i0))
    (i : block.Points) :
    Function.Injective (binaryAffineStabilizerComponent block P i) := by
  letI : MulAction.IsPretransitive block.Top block.Points := block.top_pretransitive
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq block.Top i i0
  let eTop : MulAction.stabilizer block.Top i ≃*
      MulAction.stabilizer block.Top i0 := MulAction.stabilizerEquivStabilizer hg.symm
  let e := (degreeFourZeroCoreTopStabilizerEquiv block P hr hD i).trans
    (eTop.trans (degreeFourZeroCoreTopStabilizerEquiv block P hr hD i0).symm)
  let e0 := MulEquiv.ofBijective (binaryAffineStabilizerComponent block P i0)
    ⟨hinj, binaryAffineStabilizerComponent_surjective block P i0⟩
  have hcard : Nat.card (fullFrameInducedStabilizer block P i) =
      Nat.card (LocalQuotient block P) :=
    (Nat.card_congr e.toEquiv).trans (Nat.card_congr e0.toEquiv)
  exact ((Nat.bijective_iff_surjective_and_card
    (binaryAffineStabilizerComponent block P i)).mpr
      ⟨binaryAffineStabilizerComponent_surjective block P i, hcard⟩).1

namespace DegreeFourA4OriginalPointChart
theorem originalLocalMap_injective_at (C : DegreeFourA4OriginalPointChart block)
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥)
    (i : block.Points) :
    Function.Injective (binaryAffineStabilizerComponent block P i) :=
  originalLocalMap_injective_of_one block P hr hD C.sourcePoint
    (originalLocalMap_injective block P C hr hD) i
end DegreeFourA4OriginalPointChart

namespace DegreeFourS4OriginalPointChart
theorem originalLocalMap_injective_at (C : DegreeFourS4OriginalPointChart block)
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥)
    (i : block.Points) :
    Function.Injective (binaryAffineStabilizerComponent block P i) :=
  originalLocalMap_injective_of_one block P hr hD C.sourcePoint
    (originalLocalMap_injective block P C hr hD) i
end DegreeFourS4OriginalPointChart

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
