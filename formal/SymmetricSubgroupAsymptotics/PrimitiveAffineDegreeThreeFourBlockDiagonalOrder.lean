import SymmetricSubgroupAsymptotics.BinaryPairKernelCard
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockSignedIsotypeSplit

/-!
# The literal order bound in the diagonal four-block branch

When all four coordinate sign characters agree, evaluation at one pair is
injective on the actual pair kernel.  Thus that kernel has order at most two.
The literal pair top is a subgroup of `S₄`, so the complete signed action has
order at most `2 * 24 = 48`.  This proves the order field used by the diagonal
source directly from the retained pair chart; it is not a catalogue input.
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

/-- A diagonal coordinate-sign profile makes evaluation at coordinate zero
faithful on the literal binary pair kernel. -/
theorem degreeThreeFourBlock_diagonalKernelEval_injective
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hdiag : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 1) :
    let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
    Function.Injective (fun k : C.frame.top.ker ↦ C.frame.bits k 0) := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  have hconstant : ∀ (k : C.frame.top.ker) (i j : Fin 4),
      C.frame.bits k i = C.frame.bits k j :=
    (degreeThreeFourBlockSignedIsotype_eq_one_iff_bits_constant
      block P hr hs hcomponent).mp hdiag
  change Function.Injective (fun k : C.frame.top.ker ↦ C.frame.bits k 0)
  intro x y hxy
  apply C.frame.bitsHom_injective
  apply congrArg Multiplicative.ofAdd
  funext j
  exact (hconstant x j 0).trans
    (hxy.trans (hconstant y j 0).symm)

/-- The actual pair kernel in the diagonal branch has order at most two. -/
theorem degreeThreeFourBlock_diagonalPairKernel_card_le_two
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hdiag : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 1) :
    let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
    Nat.card C.frame.top.ker ≤ 2 := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  have h := Nat.card_le_card_of_injective
    (fun k : C.frame.top.ker ↦ C.frame.bits k 0)
    (degreeThreeFourBlock_diagonalKernelEval_injective
      block P hr hs hcomponent hdiag)
  simpa only [Nat.card_zmod] using h

/-- The literal signed permutation action has order at most forty-eight in
the diagonal branch.  The proof multiplies the actual kernel and actual top
orders, so no ambient independent flip product is introduced. -/
theorem degreeThreeFourBlock_diagonalSignedAction_card_le
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hdiag : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 1) :
    let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
    Nat.card C.action ≤ 48 := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  have hkernel : Nat.card C.frame.top.ker ≤ 2 :=
    degreeThreeFourBlock_diagonalPairKernel_card_le_two
      block P hr hs hcomponent hdiag
  have htop : Nat.card C.frame.top.range ≤ 24 := by
    calc
      Nat.card C.frame.top.range ≤ Nat.card (Equiv.Perm (Fin 4)) :=
        Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
      _ = 24 := by
        rw [Nat.card_perm, Nat.card_fin]
        norm_num
  have hcard := C.frame.top.ker.card_mul_index
  rw [Subgroup.index_ker] at hcard
  calc
    Nat.card C.action =
        Nat.card C.frame.top.ker * Nat.card C.frame.top.range := hcard.symm
    _ ≤ 2 * 24 := Nat.mul_le_mul hkernel htop
    _ = 48 := by norm_num

/-- Pull the literal action order bound back through the exact signed-quotient
equivalence retained by the pair chart. -/
theorem degreeThreeFourBlock_diagonalSignedQuotient_card_le
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hdiag : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 1) :
    Nat.card (preE7NonPairAction w U ⧸ E block P) ≤ 48 := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  calc
    Nat.card (preE7NonPairAction w U ⧸ E block P) = Nat.card C.action :=
      Nat.card_congr C.sourceEquiv.toEquiv
    _ ≤ 48 := degreeThreeFourBlock_diagonalSignedAction_card_le
      block P hr hs hcomponent hdiag

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
