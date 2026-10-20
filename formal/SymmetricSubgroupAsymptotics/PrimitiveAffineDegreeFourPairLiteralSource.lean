import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourPairTableSource
import SymmetricSubgroupAsymptotics.PermutationStabilizerTransport

/-! The nontrivial-pair-kernel frame branch from a literal permutation
match. Both the ambient and stabilizer equivalences are constructed here;
the point is the exact inverse image of zero under the chosen relabelling.
Thus a catalogue selector need supply only the actual permutation match.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
  (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- All scalar, representation, stabilizer and original-profile obligations
are discharged once an existing complete table matches the actual image
on the eight pairs. This theorem does not assert catalogue completeness. -/
def degreeFourZeroCoreSixteenPairKernelBounds_of_literal_table
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥)
    {I : Type} [Finite I] (F : BinaryPairFrame block.Top I)
    (hker : F.top.ker ≠ ⊥) (hcard : Nat.card I = 8)
    (T : GeneratedTopData) (C : GeneratedTopTable T)
    (points : I ≃ Fin 8) (g : Equiv.Perm (Fin 8))
    (matched : MulAut.conj g • relabelSubgroup points F.top.range = T.literalAction) :
    DegreeFourZeroCoreFiniteFrameBounds block P 10 := by
  let eS := PermutationStabilizerTransport.groupEquiv
    F.top.range T.literalAction points g matched
  let i : I := (PermutationStabilizerTransport.pointEquiv points g).symm 0
  let ePoint := PermutationStabilizerTransport.stabilizerEquiv
    F.top.range T.literalAction points g matched 0
  let eG : F.top.range ≃* T.ModelGroup := eS.trans T.actionModelEquiv
  let eH : F.pairTopStabilizer i ≃* T.sourceStabilizer :=
    ePoint.trans T.sourceStabilizerEquivLiteral.symm
  apply degreeFourZeroCoreSixteenPairKernelBounds_of_table
    block P hr hD F hker hcard i T C eG eH
  intro h
  have hh := T.sourceStabilizerEquivLiteral_model
    (T.sourceStabilizerEquivLiteral.symm (ePoint h))
  simpa only [MulEquiv.apply_symm_apply] using hh

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
