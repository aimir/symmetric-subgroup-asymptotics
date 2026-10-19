import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightSharedTops

/-! Actual cardinal bindings for the six two-generator natural-module tops.
No abstract family name or order-only action recognition is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops

theorem top1_ternary_card : Nat.card top1.top = 2^3*3 := by
  letI : Group PrimitiveAffineEightFrameRow0TopCertificate.Source := PrimitiveAffineEightFrameRow0TopCertificate.group
  change Nat.card (Subgroup.closure (Set.range PrimitiveAffineEightFrameRow0TopCertificate.generators)) = _
  rw [← Nat.card_congr PrimitiveAffineEightFrameRow0TopCertificate.originalEquiv.toEquiv,
    PrimitiveAffineEightFrameRow0TopCertificate.source_card]
  norm_num

theorem top2_ternary_card : Nat.card top2.top = 2^3*3 := by
  letI : Group PrimitiveAffineEightFrameRow1TopCertificate.Source := PrimitiveAffineEightFrameRow1TopCertificate.group
  change Nat.card (Subgroup.closure (Set.range PrimitiveAffineEightFrameRow1TopCertificate.generators)) = _
  rw [← Nat.card_congr PrimitiveAffineEightFrameRow1TopCertificate.originalEquiv.toEquiv,
    PrimitiveAffineEightFrameRow1TopCertificate.source_card]
  norm_num

theorem top6_ternary_card : Nat.card top6.top = 2^4*3 := by
  letI : Group PrimitiveAffineEightFrameRow8TopCertificate.Source := PrimitiveAffineEightFrameRow8TopCertificate.group
  change Nat.card (Subgroup.closure (Set.range PrimitiveAffineEightFrameRow8TopCertificate.generators)) = _
  rw [← Nat.card_congr PrimitiveAffineEightFrameRow8TopCertificate.originalEquiv.toEquiv,
    PrimitiveAffineEightFrameRow8TopCertificate.source_card]
  norm_num

theorem top11_ternary_card : Nat.card top11.top = 2^3*3 := by
  letI : Group PrimitiveAffineEightFrameRow20TopCertificate.Source := PrimitiveAffineEightFrameRow20TopCertificate.group
  change Nat.card (Subgroup.closure (Set.range PrimitiveAffineEightFrameRow20TopCertificate.generators)) = _
  rw [← Nat.card_congr PrimitiveAffineEightFrameRow20TopCertificate.originalEquiv.toEquiv,
    PrimitiveAffineEightFrameRow20TopCertificate.source_card]
  norm_num

theorem top12_ternary_card : Nat.card top12.top = 2^5*3 := by
  letI : Group PrimitiveAffineEightFrameRow21TopCertificate.Source := PrimitiveAffineEightFrameRow21TopCertificate.group
  change Nat.card (Subgroup.closure (Set.range PrimitiveAffineEightFrameRow21TopCertificate.generators)) = _
  rw [← Nat.card_congr PrimitiveAffineEightFrameRow21TopCertificate.originalEquiv.toEquiv,
    PrimitiveAffineEightFrameRow21TopCertificate.source_card]
  norm_num

theorem top15_ternary_card : Nat.card top15.top = 2^6*3 := by
  letI : Group PrimitiveAffineEightFrameTop15TopCertificate.Source := PrimitiveAffineEightFrameTop15TopCertificate.group
  change Nat.card (Subgroup.closure (Set.range PrimitiveAffineEightFrameTop15TopCertificate.generators)) = _
  rw [← Nat.card_congr PrimitiveAffineEightFrameTop15TopCertificate.originalEquiv.toEquiv,
    PrimitiveAffineEightFrameTop15TopCertificate.source_card]
  norm_num

end SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops
