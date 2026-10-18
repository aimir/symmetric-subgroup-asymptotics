import SymmetricSubgroupAsymptotics.BinaryPairFrameTwoSignKernel
import SymmetricSubgroupAsymptotics.DoubleCentralBinaryRecursiveComparison
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreePostFourOneSignComparison

/-!
# The post-four two-sign comparison

For the literal degree-three signed quotient, two coordinate signs identify
the pair kernel with `C₂²`.  Its diagonal axis is central, and the quotient
of the pair kernel by that axis is central after passing to the quotient.
The universal comparator `(top × C₂) × C₂` therefore controls all
normal quotients of the signed quotient.  Appending two regular binary
orbits to the actual top realizes this comparator faithfully in degree
`s+4`.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

private abbrev C2 := Multiplicative (ZMod 2)

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

private abbrev TwoSignFrame
    (hr : Nat.card block.Fibre = 3) :=
  degreeThreeSignedQuotientPairFrame block P hr

/-- The actual projective top in the two-sign branch. -/
abbrev DegreeThreePostFourTwoSignTop
    (hr : Nat.card block.Fibre = 3) :=
  DegreeThreePostFourOneSignTop block P hr

/-- The projective kernel is literally the pair kernel, transported through
the signed-quotient equivalence. -/
def degreeThreePostFourTwoSignProjectiveKernelEquiv
    (hr : Nat.card block.Fibre = 3) :
    (degreeThreePostFourOneSignProjectiveMap block P hr).ker ≃*
      (TwoSignFrame block P hr).top.ker where
  toFun z := ⟨degreeThreeSignedQuotientRangeEquiv block P z.1,
    congrArg Subtype.val z.2⟩
  invFun k := ⟨(degreeThreeSignedQuotientRangeEquiv block P).symm k.1, by
    apply Subtype.ext
    simpa only [degreeThreePostFourOneSignProjectiveMap,
      MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply] using k.2⟩
  left_inv z := by
    apply Subtype.ext
    exact (degreeThreeSignedQuotientRangeEquiv block P).symm_apply_apply z.1
  right_inv k := by
    apply Subtype.ext
    exact (degreeThreeSignedQuotientRangeEquiv block P).apply_symm_apply k.1
  map_mul' a b := by
    apply Subtype.ext
    exact map_mul (degreeThreeSignedQuotientRangeEquiv block P) a.1 b.1

/-- The two-sign projective kernel has exact order four. -/
theorem degreeThreePostFourTwoSignProjectiveKernel_card
    (hr : Nat.card block.Fibre = 3)
    (hcomponent : Nat.card block.Component = 6)
    (htwo : Nat.card (BinaryPairFrame.CoordinateSign
      (TwoSignFrame block P hr)) = 2) :
    Nat.card (degreeThreePostFourOneSignProjectiveMap block P hr).ker = 4 := by
  let F := TwoSignFrame block P hr
  have htrans : MulAction.IsPretransitive (quotientAction block P).range
      (Fin (quotientDegree block)) :=
    degreeThreeSignedQuotientRange_pretransitive block P hr hcomponent
  calc
    Nat.card (degreeThreePostFourOneSignProjectiveMap block P hr).ker =
        Nat.card F.top.ker :=
      Nat.card_congr
        (degreeThreePostFourTwoSignProjectiveKernelEquiv block P hr).toEquiv
    _ = 4 := BinaryPairFrame.top_ker_card_eq_four_of_sign_count_two
      F htrans htwo

/-- The canonical diagonal axis of the literal pair kernel, transported
back to the signed quotient. -/
noncomputable def degreeThreePostFourTwoSignProjectiveCentralAxis
    (hr : Nat.card block.Fibre = 3)
    (hcomponent : Nat.card block.Component = 6)
    (htwo : Nat.card (BinaryPairFrame.CoordinateSign
      (TwoSignFrame block P hr)) = 2) :
    CentralOrderTwoKernelAxis
      (degreeThreePostFourOneSignProjectiveMap block P hr) := by
  let F := TwoSignFrame block P hr
  have htrans : MulAction.IsPretransitive (quotientAction block P).range
      (Fin (quotientDegree block)) :=
    degreeThreeSignedQuotientRange_pretransitive block P hr hcomponent
  let A := BinaryPairFrame.twoSignTopCentralAxis F htrans htwo
  apply A.mapDomainEquiv
    (degreeThreeSignedQuotientRangeEquiv block P).symm
    (degreeThreePostFourOneSignProjectiveMap block P hr)
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  simp only [degreeThreePostFourOneSignProjectiveMap,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply]
  rfl

/-- Two central binary factors for the literal two-sign projective kernel. -/
noncomputable def degreeThreePostFourTwoSignProjectiveCentralSeries
    (hr : Nat.card block.Fibre = 3)
    (hcomponent : Nat.card block.Component = 6)
    (htwo : Nat.card (BinaryPairFrame.CoordinateSign
      (TwoSignFrame block P hr)) = 2) :
    BinaryNormalKernelCentralSeries
      (preE7NonPairAction w U ⧸ E block P)
      (degreeThreePostFourOneSignProjectiveMap block P hr).ker :=
  (degreeThreePostFourTwoSignProjectiveCentralAxis
    block P hr hcomponent htwo).toCentralSeries (by
      rw [degreeThreePostFourTwoSignProjectiveKernel_card
        block P hr hcomponent htwo])

/-- Universal recursive comparison for every normal quotient in the
post-four two-sign branch. -/
noncomputable def degreeThreePostFourTwoSignComparison
    (hr : Nat.card block.Fibre = 3)
    (hcomponent : Nat.card block.Component = 6)
    (htwo : Nat.card (BinaryPairFrame.CoordinateSign
      (TwoSignFrame block P hr)) = 2) :
    CentralBinaryRecursiveComparison
      (DoubleCentralBinaryRecursiveComparison.Comparator
        (DegreeThreePostFourTwoSignTop block P hr))
      (preE7NonPairAction w U ⧸ E block P)
      ((preE7NonPairAction w U ⧸ E block P) ⧸
        (degreeThreePostFourTwoSignProjectiveCentralSeries
          block P hr hcomponent htwo).C) :=
  DoubleCentralBinaryRecursiveComparison.centralSeriesComparison
    (DegreeThreePostFourTwoSignTop block P hr)
    (degreeThreePostFourOneSignProjectiveMap block P hr)
    (degreeThreePostFourOneSignProjectiveMap_surjective block P hr)
    (degreeThreePostFourTwoSignProjectiveCentralSeries
      block P hr hcomponent htwo)
    (by rw [degreeThreePostFourTwoSignProjectiveKernel_card
      block P hr hcomponent htwo])

/-- Faithful action of the universal comparator on the actual top points
plus two disjoint binary orbits. -/
def degreeThreePostFourTwoSignComparatorAction
    (hr : Nat.card block.Fibre = 3) :
    DoubleCentralBinaryRecursiveComparison.Comparator
        (DegreeThreePostFourTwoSignTop block P hr) →*
      Equiv.Perm (Fin ((Nat.card block.Points + 2) + 2)) :=
  DegreeThreeFourBlockTwoSignComparator.appendC2Action
    (DegreeThreeFourBlockTwoSignComparator.appendC2Action
      (degreeThreePostFourOneSignTopAction block P hr))

theorem degreeThreePostFourTwoSignComparatorAction_injective
    (hr : Nat.card block.Fibre = 3) :
    Function.Injective
      (degreeThreePostFourTwoSignComparatorAction block P hr) :=
  DegreeThreeFourBlockTwoSignComparator.appendC2Action_injective
    (DegreeThreeFourBlockTwoSignComparator.appendC2Action
      (degreeThreePostFourOneSignTopAction block P hr))
    (DegreeThreeFourBlockTwoSignComparator.appendC2Action_injective
      (degreeThreePostFourOneSignTopAction block P hr)
      (degreeThreePostFourOneSignTopAction_injective block P hr))

/-- The literal faithful `s+4` point comparator. -/
abbrev DegreeThreePostFourTwoSignComparator
    (hr : Nat.card block.Fibre = 3) :=
  (degreeThreePostFourTwoSignComparatorAction block P hr).range

/-- Identification of the abstract universal comparator with its literal
permutation image. -/
def degreeThreePostFourTwoSignComparatorEquiv
    (hr : Nat.card block.Fibre = 3) :
    DoubleCentralBinaryRecursiveComparison.Comparator
        (DegreeThreePostFourTwoSignTop block P hr) ≃*
      DegreeThreePostFourTwoSignComparator block P hr :=
  MonoidHom.ofInjective
    (degreeThreePostFourTwoSignComparatorAction_injective block P hr)

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
