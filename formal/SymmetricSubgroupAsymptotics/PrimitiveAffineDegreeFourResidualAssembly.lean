import SymmetricSubgroupAsymptotics.PrimitiveAffineFinalPartialAssembly
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourCoarseNonzeroMenu

/-!
# Assembly of the degree-four affine residual lane

The numerical affine exhaustion leaves the explicit degree-four block-count
menu recorded by `IsDegreeFourTwentyFourExceptionalBlockCount`.  On that
menu a nonzero literal ternary core has the complete character interval
proved in `PrimitiveAffineDegreeFourCoarseNonzeroMenu`; the actual earlier
owner is `ACOMP`, as for the already integrated degree-five and degree-nine
affine character intervals.

This file isolates that finished half and gives the final dispatcher a
single zero-core endpoint.  The endpoint is a construction boundary, not a
literature assumption: the adjacent zero-core files instantiate it from the
finite frames and the proved large-block exhaustion.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- Every block count in the literal degree-four residual menu is at most
`3072`.  The maximum is the last mixed pair-frame count `3 * 2^10`; the
remaining six exceptional values are at most sixty. -/
theorem degreeFourTwentyFourExceptionalBlockCount_le_3072
    {s : ℕ}
    (hs : ComponentSource.IsDegreeFourTwentyFourExceptionalBlockCount s) :
    s ≤ 3072 := by
  rcases hs with hs | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases hs with ⟨a, _ha1, ha8, rfl⟩ | ⟨a, ha10, rfl⟩
    · calc
        2 ^ a ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) ha8
        _ ≤ 3072 := by norm_num
    · calc
        3 * 2 ^ a ≤ 3 * 2 ^ 10 :=
          Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by norm_num) ha10)
        _ = 3072 := by norm_num
  all_goals norm_num

/-- The zero-core construction boundary left after the nonzero Tracey menu.
It receives the literal degree-four exception witness, so its implementation
can invoke the proved zero-core exceptional exhaustion without reconstructing
or widening the finite menu. -/
abbrev DegreeFourZeroCoreResidualSource :=
  ∀ {w : ℕ} (U : PreE7NonPairActionClass w) (_hw : 5 ≤ w)
    (basePoint : Fin w)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre],
    ImprimitiveAffineResidualCapacityException
        (Nat.card block.Fibre) (Nat.card block.Points)
        (Nat.card block.Component) →
    Nat.card block.Fibre = 4 →
    ComponentSource.IsDegreeFourTwentyFourExceptionalBlockCount
        (Nat.card block.Points) →
    degreeFourTernaryCore block P = ⊥ →
    PreE7RankTailSourceOrYonedaTopData w U

/-- The nonzero-core half of the final degree-four residual source.  It uses
the exact `ACOMP` character owner already assigned to affine component
intervals and derives the finite width bound from the retained numerical
exception witness. -/
noncomputable def degreeFourNonzeroResidualSource
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (hTracey : TraceySolubleOrbitInducedModuleInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    {w : ℕ} (U : PreE7NonPairActionClass w) (_hw : 5 ≤ w)
    (basePoint : Fin w)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (_hres : ImprimitiveAffineResidualCapacityException
      (Nat.card block.Fibre) (Nat.card block.Points)
      (Nat.card block.Component))
    (hr : Nat.card block.Fibre = 4)
    (hs : ComponentSource.IsDegreeFourTwentyFourExceptionalBlockCount
      (Nat.card block.Points))
    (hD : degreeFourTernaryCore block P ≠ ⊥) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  exact degreeFourNonzeroCharacterIntervalSource block P hZmud lit .acomp
    hTracey hMN hClifford hTraceyPerm hr block.degrees_ge_two.2
    (degreeFourTwentyFourExceptionalBlockCount_le_3072 hs) hD

/-- Exhaust the complete degree-four residual lane once the adjacent
zero-core endpoint has been supplied.  The case split is on the literal
capacity-exception constructor and on the literal ternary core; no new
classification or counting premise is introduced here. -/
noncomputable def degreeFourResidualSource_of_zeroCore
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (hTracey : TraceySolubleOrbitInducedModuleInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hClifford : CliffordHomogeneousRestriction.Input)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (zeroCore : DegreeFourZeroCoreResidualSource) :
    PrimitiveAffineResidualDegreeSource 4 := by
  intro w U hw basePoint block P hres hr
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hr]; norm_num)
  refine Classical.choice ?_
  cases hcap : hres.toCapacityException with
  | degreeTwo hr' hs => omega
  | degreeThree hr' hs => omega
  | degreeFive hr' hs => omega
  | degreeEight hr' hs => omega
  | degreeNine hr' hs => omega
  | degreeSixteen hr' hs => omega
  | degreeFour hr' hs =>
      by_cases hD : degreeFourTernaryCore block P = ⊥
      · exact ⟨zeroCore U hw basePoint block P hres hr hs hD⟩
      · exact ⟨degreeFourNonzeroResidualSource hZmud lit hTracey hMN
          hClifford hTraceyPerm U hw basePoint block P hres hr hs hD⟩

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
