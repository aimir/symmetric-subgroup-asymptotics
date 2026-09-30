import SymmetricSubgroupAsymptotics.BinaryCarrierIdentitySlotNaturality
import SymmetricSubgroupAsymptotics.BinaryCarrierKernelNaturalizedReflection

/-!
# Kernel-first naturalizer for quotient-identity cells

The replacement kernel of a quotient-identity cell is the retained
annihilator.  Once target equality identifies that kernel after transport,
the underlying normal axis is forced.  The action equivalence then descends
to the quotient groups and supplies the two commuting squares required by
the simultaneous reflection theorem.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryCarrierIdentityKernelNaturalizer

open SymmetricSubgroupAsymptotics
open BinaryCarrierIdentitySlotNaturality
open BinaryCarrierKernelNaturalizedReflection
open BinaryCarrierMenuSlots
open BinaryCarrierProfileTransport

/-- The canonical kernel-first quotient square for two identity slots. -/
def quotientSquare
    (g h : MixtureKind)
    (N : Subgroup (mixtureAction g))
    (M : Subgroup (mixtureAction h))
    [N.Normal] [M.Normal]
    (e : mixtureAction g ≃* mixtureAction h)
    (hkernel :
      (quotientIdentitySlot g N).beta.ker.map
          (identityCarrierEquiv g e).toMonoidHom =
        (quotientIdentitySlot h M).beta.ker) :
    QuotientSquare
      (quotientIdentitySlot g N).alpha
      (quotientIdentitySlot h M).alpha
      (quotientIdentitySlot g N).beta
      (quotientIdentitySlot h M).beta e
      (identityCarrierEquiv g e) := by
  let haxis : N.map e.toMonoidHom = M :=
    axis_map_eq_of_betaKer_map_eq g N M e hkernel
  exact
    { quotientEquiv := quotientEquiv g N M e haxis
      alpha_intertwine := alpha_intertwine g N M e haxis
      beta_intertwine := beta_intertwine g N M e haxis }

end SymmetricSubgroupAsymptotics.BinaryCarrierIdentityKernelNaturalizer

end
