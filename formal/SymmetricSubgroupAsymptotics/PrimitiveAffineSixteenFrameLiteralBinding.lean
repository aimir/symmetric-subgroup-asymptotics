import SymmetricSubgroupAsymptotics.BinaryConjugacyTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourZeroCoreTopEquiv

/-!
# Literal top binding for sixteen-block affine frames

This is the degree-sixteen analogue of the already checked eight-block
binding.  It retains an exact relabelling and ambient conjugacy between the
actual block top and a literal permutation top, followed by the finite
model equivalence used by the generated certificates.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- Exact top-only identification of an actual sixteen-block zero-core
quotient with one generated finite model. -/
structure DegreeFourZeroCoreSixteenLiteralTopMatch
    (ModelGroup : Type) [Group ModelGroup] : Type 1 where
  literalAction : Subgroup (Equiv.Perm (Fin 16))
  actionModelEquiv : literalAction ≃* ModelGroup
  pointEquiv : block.Points ≃ Fin 16
  conjugator : Equiv.Perm (Fin 16)
  conjugated :
    MulAut.conj conjugator •
      relabelSubgroup pointEquiv block.Top = literalAction

namespace DegreeFourZeroCoreSixteenLiteralTopMatch

/-- Compose the structural zero-core quotient map with the literal top
identification and the generated finite model. -/
noncomputable def groupEquiv
    {ModelGroup : Type} [Group ModelGroup]
    (M : DegreeFourZeroCoreSixteenLiteralTopMatch block ModelGroup)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥) :
    DegreeFourComplementQuotient block P ≃* ModelGroup :=
  (degreeFourZeroCoreTopEquiv block P hr hD).trans
    ((M.pointEquiv.permCongrHom.subgroupMap block.Top).trans
      ((actionConjugacyEquiv M.conjugator M.conjugated).trans
        M.actionModelEquiv))

end DegreeFourZeroCoreSixteenLiteralTopMatch
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
