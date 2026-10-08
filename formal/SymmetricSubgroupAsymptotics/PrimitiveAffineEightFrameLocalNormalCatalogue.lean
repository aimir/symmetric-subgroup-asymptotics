import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameLocalRowCatalogue
import SymmetricSubgroupAsymptotics.FiniteSurjectiveKernelTransport

/-!
# Complete local quotient catalogues from finite normal-state registries

For a fixed literal eight-point top, an eligible local row is determined by
the kernel of its onto map from the point stabilizer.  This file packages the
reusable argument: a complete normal-state registry only has to identify the
states of index three, and the noncommutative states of index six.  Every
other state is irrelevant to the affine local component.

The structure below is the small checked boundary used by the remaining
finite eight-frame tops.  Its `complete` field is supplied by the generic
normal-join registry; its `classify` field is a finite statement about the
emitted states.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- A complete normal-state list in one literal point stabilizer, together
with the exact eligible kernel carried by each relevant state.  An index-six
state may instead be marked commutative, since the actual faithful binary
plane quotient of order six is noncommutative. -/
structure DegreeEightLiteralLocalNormalCatalogue
    (T : Subgroup (Equiv.Perm (Fin 8))) : Type 1 where
  Row : Type
  row : Row → DegreeEightLiteralLocalRow T
  State : Type
  state : State → Subgroup (MulAction.stabilizer T (0 : Fin 8))
  complete : ∀ (N : Subgroup (MulAction.stabilizer T (0 : Fin 8)))
    [N.Normal], ∃ s, state s = N
  classify : ∀ s,
    (∃ r, state s = (row r).literalLocalMap.ker) ∨
    ((state s).index ≠ 3 ∧ (state s).index ≠ 6) ∨
    ((state s).index = 6 ∧
      ∃ _normal : (state s).Normal,
        IsMulCommutative
          (MulAction.stabilizer T (0 : Fin 8) ⧸ (state s)))

namespace DegreeEightLiteralLocalNormalCatalogue

variable {T : Subgroup (Equiv.Perm (Fin 8))}

/-- A complete normal-state classification gives the exact map-level local
row catalogue.  The target equivalence is reconstructed from equality of
kernels, so no order-only action match enters the finite-frame consumer. -/
noncomputable def toLocalRowCatalogue
    (C : DegreeEightLiteralLocalNormalCatalogue T) :
    DegreeEightLiteralLocalRowCatalogue T where
  Row := C.Row
  row := C.row
  complete := by
    intro L _ _ f hf hcard
    obtain ⟨s, hs⟩ := C.complete f.ker
    have hindex : f.ker.index = Nat.card L := by
      rw [Subgroup.index_ker, f.range_eq_top_of_surjective hf,
        Nat.card_congr Subgroup.topEquiv.toEquiv]
    have hstateIndex : (C.state s).index = Nat.card L := by
      rw [hs]
      exact hindex
    rcases C.classify s with hrow | hout | hcomm
    · obtain ⟨r, hr⟩ := hrow
      have hkernels : f.ker = (C.row r).literalLocalMap.ker :=
        hs.symm.trans hr
      refine ⟨r,
        surjectiveTargetEquivOfKernelEq f (C.row r).literalLocalMap
          hf (C.row r).literalLocalMap_surjective hkernels,
        surjectiveTargetEquivOfKernelEq_comp f (C.row r).literalLocalMap
          hf (C.row r).literalLocalMap_surjective hkernels⟩
    · rcases hout with ⟨hthree, hsix⟩
      rcases hcard with hL | ⟨hL, _⟩
      · exact False.elim (hthree (hstateIndex.trans hL))
      · exact False.elim (hsix (hstateIndex.trans hL))
    · rcases hcomm with ⟨hsix, hnormal, hcomm⟩
      rcases hcard with hL | ⟨hL, hnoncomm⟩
      · omega
      · apply False.elim
        apply hnoncomm
        letI : (C.state s).Normal := hnormal
        let e :
            (MulAction.stabilizer T (0 : Fin 8) ⧸ (C.state s)) ≃* L :=
          (QuotientGroup.quotientMulEquivOfEq hs).trans
            (QuotientGroup.quotientKerEquivOfSurjective f hf)
        refine ⟨⟨fun x y => ?_⟩⟩
        obtain ⟨a, rfl⟩ := e.surjective x
        obtain ⟨b, rfl⟩ := e.surjective y
        rw [← map_mul, hcomm.is_comm.comm a b, map_mul]

end DegreeEightLiteralLocalNormalCatalogue
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
