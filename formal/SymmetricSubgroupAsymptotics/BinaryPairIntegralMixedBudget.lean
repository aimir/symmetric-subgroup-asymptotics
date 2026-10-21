import SymmetricSubgroupAsymptotics.BinaryPairIntegralMixedLargeSection
import SymmetricSubgroupAsymptotics.NormalIntegralCoinvariantExactIntersection
import SymmetricSubgroupAsymptotics.NormalKernelIntersectionCard

/-! The extra mixed commutator is paid in the exact integral intersection
identity. The same E, kernel intersection and actual top image occur on
both sides, including every possible higher cyclic factor. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X I : Type} [Finite X] [Finite I]
    {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U I)
    [MulAction.IsPretransitive F.top.range I]

/-- A nontrivial contained cut plus a genuine mixed element gives at
least four elements in the actual commutator intersection. -/
theorem four_le_actual_commutator_intersection_of_large_section
    (hU : IsPGroup 2 U) (i : I)
    (E L : Subgroup U) [E.Normal] [L.Normal]
    (hlarge : Nat.card I < 2 * Module.finrank (ZMod 2)
      (F.kernelSpace ⧸ F.normalSpace L))
    (hE : ¬ E ≤ F.top.ker)
    (hL : L ≤ ⁅E, (⊤ : Subgroup U)⁆ ⊓ F.top.ker)
    (hLcard : 2 ≤ Nat.card L) :
    4 ≤ Nat.card (⁅E, (⊤ : Subgroup U)⁆ ⊓ F.top.ker : Subgroup U) := by
  have hnot := F.commutator_intersection_not_le_of_large_section hU i E L hlarge hE
  have hc := two_mul_inf_card_le_of_not_le L
    (⁅E, (⊤ : Subgroup U)⁆ ⊓ F.top.ker) hnot
  rw [inf_eq_left.mpr hL] at hc
  omega

/-- The four-dimensional exceptional intersection is sufficient once
its surviving original section is large. This is an integral bound. -/
theorem integral_order_le_four_mul_top_of_large_mixed_cut
    (hU : IsPGroup 2 U) (i : I)
    (E L : Subgroup U) [E.Normal] [L.Normal]
    (hlarge : Nat.card I < 2 * Module.finrank (ZMod 2)
      (F.kernelSpace ⧸ F.normalSpace L))
    (hE : ¬ E ≤ F.top.ker)
    (hL : L ≤ ⁅E, (⊤ : Subgroup U)⁆ ⊓ F.top.ker)
    (hLcard : 2 ≤ Nat.card L)
    (hAcard : Nat.card (E ⊓ F.top.ker : Subgroup U) ≤ 16) :
    normalIntegralCoinvariantOrder E ≤
      4 * normalIntegralCoinvariantOrder (E.map F.top.rangeRestrict) := by
  have hc := F.four_le_actual_commutator_intersection_of_large_section
    hU i E L hlarge hE hL hLcard
  apply normalIntegralCoinvariantOrder_le_of_actual_intersection_budget
    F.top.rangeRestrict F.top.rangeRestrict_surjective E 4
  simpa only [MonoidHom.ker_rangeRestrict] using
    (show Nat.card (E ⊓ F.top.ker : Subgroup U) ≤
      4 * Nat.card (⁅E, (⊤ : Subgroup U)⁆ ⊓ F.top.ker : Subgroup U) by omega)

end SymmetricSubgroupAsymptotics.BinaryPairFrame
