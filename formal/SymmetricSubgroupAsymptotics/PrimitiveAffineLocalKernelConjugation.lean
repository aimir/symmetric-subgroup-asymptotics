import SymmetricSubgroupAsymptotics.PrimitiveAffineBinaryExceptionalLocal

/-!
# Local affine-kernel conjugation in compressed coordinates

The compressed local quotient acts on the literal affine translation
kernel through the transported complement representation.  This file makes
that compatibility pointwise.  It is the local identity needed to turn the
wreath-coordinate conjugation formula into a diagonal action on the global
translation submodule.
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

/-- Conjugation in the literal local kernel is the exact transported linear
action of the compressed local complement. -/
theorem localKernelEquiv_conjugation
    (g : block.Component) (z : (localMap block P).ker) :
    ((localKernelEquiv block P).symm (MulAut.conjNormal g z)).toAdd =
      (binaryAffineLocalLinearRepresentation block P).ρ
        (localMap block P g)
        ((localKernelEquiv block P).symm z).toAdd := by
  letI : MulAction.IsPreprimitive block.Component block.Fibre := primitive block
  let C := chart block P
  letI : Fact P.p.Prime := C.primeFact
  let δ := binaryAffineLocalComplementEquiv block P
  let c : P.complement (origin block) := δ.symm (localMap block P g)
  have hc : c = P.complementProjection (origin block) g := by
    apply δ.injective
    rw [δ.apply_symm_apply]
    apply Subtype.ext
    rfl
  let v : C.V := ((localKernelEquiv block P).symm z).toAdd
  apply Multiplicative.ofAdd.injective
  simp only [ofAdd_toAdd]
  apply (localKernelEquiv block P).injective
  rw [(localKernelEquiv block P).apply_symm_apply]
  apply Subtype.ext
  change g * z.1 * g⁻¹ =
    (((P.bottomKernelEquiv (primitive block) C (origin block))
      (Multiplicative.ofAdd
        ((P.complementRepresentation
          (primitive block) C (origin block)).ρ c v)) :
        (P.complementProjection (origin block)).ker) : block.Component)
  rw [P.bottomKernelEquiv_coe, P.complementRepresentation_apply]
  simp only [ofAdd_toAdd, C.equiv.symm_apply_apply]
  rw [hc, P.complementAction_projection]
  change g * z.1 * g⁻¹ =
    (MulAut.conjNormal g
      (C.equiv.symm (Multiplicative.ofAdd v) : P.V) : block.Component)
  have hz : (z.1 : block.Component) =
      (C.equiv.symm (Multiplicative.ofAdd v) : P.V) := by
    change z.1 =
      (localKernelEquiv block P (Multiplicative.ofAdd v)).1
    exact congrArg Subtype.val
      ((localKernelEquiv block P).apply_symm_apply z).symm
  rw [hz]
  rfl
  all_goals exact primitive block

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
