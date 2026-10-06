import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourZeroCoreSource

/-!
# The zero-core complement is the literal block top

In degree four the quotient after translations always surjects onto the
actual block top.  Vanishing ternary core makes the same map injective.
This exact equivalence is the structural entry point for the eight-point
finite catalogue.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- Exact identification of the zero-core complement quotient with its
literal transitive block top. -/
def degreeFourZeroCoreTopEquiv
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥) :
    DegreeFourComplementQuotient block P ≃* block.Top := by
  apply MulEquiv.ofBijective (degreeFourQuotientTopMap block P)
  constructor
  · intro x y hxy
    apply degreeFourZeroCoreTopAction_injective block P hr hD
    exact congrArg
      (fun q : block.Top ↦
        (Finite.equivFin block.Points).permCongrHom q.1) hxy
  · exact degreeFourQuotientTopMap_surjective block P

@[simp]
theorem degreeFourZeroCoreTopEquiv_apply
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (q : DegreeFourComplementQuotient block P) :
    degreeFourZeroCoreTopEquiv block P hr hD q =
      degreeFourQuotientTopMap block P q := rfl

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
