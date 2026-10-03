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

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
