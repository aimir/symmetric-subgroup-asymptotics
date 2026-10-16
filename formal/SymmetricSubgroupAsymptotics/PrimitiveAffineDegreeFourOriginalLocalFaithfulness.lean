import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourA4OriginalGroupChart
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourS4OriginalGroupChart
import SymmetricSubgroupAsymptotics.BinaryFourS4OriginalInducedChart

/-! The original local epimorphism is faithful in the zero-core A4/S4
four-block cases. This retains the actual source stabilizer and local map;
the S4 exclusion uses the previously checked canonical reflection proof. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]

namespace DegreeFourS4OriginalPointChart

theorem originalLocalMap_injective (C : DegreeFourS4OriginalPointChart block)
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥) :
    Function.Injective (binaryAffineStabilizerComponent block P C.sourcePoint) := by
  let eH := stabilizerEquiv (block := block) (P := P) (C := C) hr hD
  let f := binaryAffineStabilizerComponent block P C.sourcePoint
  have hf : Function.Surjective f := binaryAffineStabilizerComponent_surjective block P _
  have htarget : Nat.card (LocalQuotient block P) = 6 := by
    rcases degreeFourZeroCoreTopStabilizerLocalTarget_card block P hr with h3 | h6
    · exact False.elim
        (BinaryFourS4OriginalInducedChart.canonicalLocal_no_card_three_quotient
          (f.comp eH.symm.toMonoidHom) (hf.comp eH.symm.surjective) h3)
    · exact h6
  have hsource : Nat.card (fullFrameInducedStabilizer block P C.sourcePoint) = 6 :=
    (Nat.card_congr eH.toEquiv).trans
      BinaryFourCanonicalSymmetricInducedChart.stabilizer_card
  exact ((Nat.bijective_iff_surjective_and_card f).mpr
    ⟨hf, hsource.trans htarget.symm⟩).1

end DegreeFourS4OriginalPointChart

namespace DegreeFourA4OriginalPointChart

theorem originalLocalMap_injective (C : DegreeFourA4OriginalPointChart block)
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥) :
    Function.Injective (binaryAffineStabilizerComponent block P C.sourcePoint) := by
  let eH := stabilizerEquiv (block := block) (P := P) (C := C) hr hD
  let f := binaryAffineStabilizerComponent block P C.sourcePoint
  have hf : Function.Surjective f := binaryAffineStabilizerComponent_surjective block P _
  have hsource : Nat.card (fullFrameInducedStabilizer block P C.sourcePoint) = 3 := by
    rw [Nat.card_congr eH.toEquiv,
      Nat.card_congr BinaryFourCanonicalInducedChart.stabilizerTernaryEquiv.toEquiv,
      Nat.card_congr (Multiplicative.toAdd : BinaryFourBlockAugmentation.Ternary ≃ ZMod 3),
      Nat.card_zmod]
  have htarget : Nat.card (LocalQuotient block P) = 3 := by
    rcases degreeFourZeroCoreTopStabilizerLocalTarget_card block P hr with h3 | h6
    · exact h3
    · have hle := Nat.card_le_card_of_surjective f hf
      change Nat.card (LocalQuotient block P) ≤
        Nat.card (fullFrameInducedStabilizer block P C.sourcePoint) at hle
      rw [hsource, h6] at hle
      omega
  exact ((Nat.bijective_iff_surjective_and_card f).mpr
    ⟨hf, hsource.trans htarget.symm⟩).1

end DegreeFourA4OriginalPointChart
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
