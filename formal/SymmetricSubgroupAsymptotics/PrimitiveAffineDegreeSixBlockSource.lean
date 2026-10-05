import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixTailSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveBlockTransfer
import SymmetricSubgroupAsymptotics.DegreeSixTernaryBlockOwner

/-!
# The high branch of a three-by-two affine block cell

An actual imprimitive affine block system with three points per block and
two blocks has ambient degree six.  If one literal normal axis has a strict
ternary head, the existing three-by-two structural theorem constructs the
normal ternary subgroup of index two on that same ambient group.  The direct
degree-six cold source then applies without passing through an abstract
action label or a newly assumed finite classification.
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

/-- The literal degree of a three-by-two block system is six. -/
theorem width_eq_six_of_three_by_two
    (hFibre : Nat.card block.Fibre = 3)
    (hPoints : Nat.card block.Points = 2) : w = 6 := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have h := width_eq block
  rw [hFibre, hPoints] at h
  omega

/-- A strict ternary axis in the actual three-by-two block system produces
the intrinsic odd-index-two witness on the unchanged ambient group. -/
theorem oddIndexWitness_of_three_by_two_high
    (hFibre : Nat.card block.Fibre = 3)
    (hPoints : Nat.card block.Points = 2)
    (N : Subgroup (preE7NonPairAction w U)) [N.Normal]
    (hHigh : 3 * w <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    Nonempty (C1OddIndexTwoOwnerWitness (preE7NonPairAction w U)) := by
  letI : MulAction.IsPretransitive
      (preE7NonPairAction w U) (Fin w) :=
    Non2TransitiveActionClass.representative_pretransitive U.1.1
  apply block.degreeSix_ternaryBlock_owner N hFibre hPoints
  simpa using hHigh

/-- In the complementary branch, every literal normal ternary head is
zero.  This is stronger than merely being outside the strict high range:
at ambient degree six even a one-dimensional ternary head satisfies the
strict `3w < 20 d₃` inequality. -/
theorem all_normal_head_zero_of_no_three_by_two_high
    (hFibre : Nat.card block.Fibre = 3)
    (hPoints : Nat.card block.Points = 2)
    (hNoHigh : ∀ (N : Subgroup (preE7NonPairAction w U)) [N.Normal],
      ¬ 3 * w <
        20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    ∀ (N : Subgroup (preE7NonPairAction w U)) [N.Normal],
      Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 0 := by
  have hw : w = 6 := width_eq_six_of_three_by_two block hFibre hPoints
  intro N hN
  by_contra hne
  have hpos : 0 <
      Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) :=
    Nat.pos_of_ne_zero hne
  exact hNoHigh N (by omega)

/-- Trivial literal fibre signs already give the intrinsic odd-index-two
owner.  This is the structural branch hidden inside the earlier high-head
argument, but it does not require a high normal axis. -/
theorem oddIndexWitness_of_three_by_two_trivialSigns
    (hFibre : Nat.card block.Fibre = 3)
    (hPoints : Nat.card block.Points = 2)
    (hSigns : DegreeThreeBlockInversionHead.coordinateSigns
      block.map block.map_equivariant = 1) :
    Nonempty (C1OddIndexTwoOwnerWitness (preE7NonPairAction w U)) := by
  letI : Fintype block.Points := Fintype.ofFinite _
  let e := block.ternaryFibreCharts hFibre
  refine ⟨{
      ternary := block.topMap.ker
      normal := inferInstance
      ternaryPGroup :=
        DegreeThreeBlockInversionHead.kernel_isPGroup_of_coordinateSigns_eq_one
          (hb := block.map_equivariant) block.map e hSigns
      index_two := ?_ }⟩
  rw [Subgroup.index_ker]
  exact block.twoBlock_top_card hPoints

/-- The high half of the degree-six exceptional affine cell is a completed
ambient source. -/
noncomputable def degreeSixSource_of_three_by_two_high
    (hKP : KovacsPraegerAbelianizationBound)
    (hFibre : Nat.card block.Fibre = 3)
    (hPoints : Nat.card block.Points = 2)
    (N : Subgroup (preE7NonPairAction w U)) [N.Normal]
    (hHigh : 3 * w <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  have hw : w = 6 := width_eq_six_of_three_by_two block hFibre hPoints
  subst w
  let W := Classical.choice
    (oddIndexWitness_of_three_by_two_high block hFibre hPoints N hHigh)
  exact PrimitiveAffineDegreeSixOddIndexTailSource.source hKP U W

/-- The trivial-sign half of the degree-six block cell is already a complete
source, independently of every relative-head inequality. -/
noncomputable def degreeSixSource_of_three_by_two_trivialSigns
    (hKP : KovacsPraegerAbelianizationBound)
    (hFibre : Nat.card block.Fibre = 3)
    (hPoints : Nat.card block.Points = 2)
    (hSigns : DegreeThreeBlockInversionHead.coordinateSigns
      block.map block.map_equivariant = 1) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  have hw : w = 6 := width_eq_six_of_three_by_two block hFibre hPoints
  subst w
  let W := Classical.choice
    (oddIndexWitness_of_three_by_two_trivialSigns
      block hFibre hPoints hSigns)
  exact PrimitiveAffineDegreeSixOddIndexTailSource.source hKP U W

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
