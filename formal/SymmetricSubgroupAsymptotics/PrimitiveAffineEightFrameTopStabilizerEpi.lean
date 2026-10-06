import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourZeroCoreTopEquiv

/-!
# The exact local epimorphism on the zero-core block top

The thirty eight-frame rows are indexed by normal kernels in a point
stabilizer of a literal degree-eight top.  This file produces the matching
epimorphism directly on the actual `block.Top`, rather than leaving it on
the quotient group before the zero-core identification.
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

/-- The quotient-top map restricts surjectively to each corresponding point
stabilizer. -/
theorem binaryAffineStabilizerTopMap_surjective (i : block.Points) :
    Function.Surjective (binaryAffineStabilizerTopMap block P i) := by
  intro q
  obtain ⟨a, ha⟩ := binaryAffineQuotientTopMap_surjective block P q.1
  have hai : a ∈ binaryAffineQuotientTopStabilizer block P i := by
    change binaryAffineQuotientTopMap block P a • i = i
    rw [ha]
    exact q.2
  refine ⟨⟨a, hai⟩, ?_⟩
  exact Subtype.ext ha

/-- Under zero core, the two literal point stabilizers are exactly
isomorphic. -/
noncomputable def degreeFourZeroCoreTopStabilizerEquiv
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (i : block.Points) :
    binaryAffineQuotientTopStabilizer block P i ≃*
      MulAction.stabilizer block.Top i :=
  MulEquiv.ofBijective (binaryAffineStabilizerTopMap block P i)
    ⟨binaryAffineStabilizerTopMap_injective_of_kernel_eq_bot block P i
        (degreeFourLinearBlockKernel_eq_bot_of_core_eq_bot block P hr hD),
      binaryAffineStabilizerTopMap_surjective block P i⟩

/-- The actual local `C3` or `S3` quotient, now defined on the point
stabilizer of the literal top. -/
def degreeFourZeroCoreTopStabilizerLocalMap
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (i : block.Points) :
    MulAction.stabilizer block.Top i →* LocalQuotient block P :=
  (binaryAffineStabilizerComponent block P i).comp
    (degreeFourZeroCoreTopStabilizerEquiv block P hr hD i).symm.toMonoidHom

/-- The local map used to select a finite frame row is onto. -/
theorem degreeFourZeroCoreTopStabilizerLocalMap_surjective
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (i : block.Points) :
    Function.Surjective
      (degreeFourZeroCoreTopStabilizerLocalMap block P hr hD i) :=
  (binaryAffineStabilizerComponent_surjective block P i).comp
    (degreeFourZeroCoreTopStabilizerEquiv block P hr hD i).symm.surjective

/-- Its target has exactly the two orders retained by the thirty-row
catalogue. -/
theorem degreeFourZeroCoreTopStabilizerLocalTarget_card
    (hr : Nat.card block.Fibre = 4) :
    Nat.card (LocalQuotient block P) = 3 ∨
      Nat.card (LocalQuotient block P) = 6 := by
  rw [localQuotient_card_eq_complement block P]
  exact degreeFour_complement_card_eq_three_or_six block P hr

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
