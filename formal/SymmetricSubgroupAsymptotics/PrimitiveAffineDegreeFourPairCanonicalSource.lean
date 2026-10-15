import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTransitiveMatch
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourPairTrivialLiteralSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourEightTopEligibility

/-! Select the actual eight-pair quotient from the fixed canonical
catalogue. A trivial pair kernel is completely discharged by the original
quotient-socle family and moving-orbit head bound. With nontrivial kernel,
the descended original local epimorphism excludes the four impossible tops. -/

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

local instance pairCanonical_transitive :
    MulAction.IsPretransitive block.Top block.Points := block.top_pretransitive

def degreeFourPairTopMatch
    (published : DegreeEightCanonicalCatalogue.PublishedClassification)
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥)
    {I : Type} [Finite I] (F : BinaryPairFrame block.Top I) (hI : Nat.card I = 8) :
    DegreeEightCanonicalCatalogue.TransitiveLiteralMatch F.top.range := by
  letI : MulAction.IsPretransitive F.top.range I := F.top_pretransitive
  exact DegreeEightCanonicalCatalogue.transitiveLiteralMatch published F.top.range hI
    (F.top_not_isPGroup (degreeFourZeroCoreTop_not_isPGroup_two block P hr hD))

/-- The faithful-pair-action branch now needs no project-owned matching or
rank premise. The normal axes remain those of the original outer profile. -/
def degreeFourZeroCoreSixteenPairTrivialBounds_of_canonical
    (published : DegreeEightCanonicalCatalogue.PublishedClassification)
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥)
    {I : Type} [Finite I] (F : BinaryPairFrame block.Top I)
    (hker : F.top.ker = ⊥) (hI : Nat.card I = 8) (x : block.Points) :
    DegreeFourZeroCoreFiniteFrameBounds block P 10 := by
  let M := degreeFourPairTopMatch block P published hr hD F hI
  exact degreeFourZeroCoreSixteenPairTrivialBounds_of_literal block P hr hD
    F hker hI x M.index M.points M.conjugator M.matched

/-- For a nontrivial pair kernel, the original local map descends onto the
actual pair-top stabilizer, so none of the four rejected literals can occur. -/
theorem degreeFourPairTopMatch_not_excluded
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥)
    {I : Type} [Finite I] (F : BinaryPairFrame block.Top I)
    (hker : F.top.ker ≠ ⊥)
    (M : DegreeEightCanonicalCatalogue.TransitiveLiteralMatch F.top.range) :
    ¬ DegreeFourEightTopEligibility.Excluded M.index := by
  intro hj
  let T := (DegreeTwoPairedEightSharedTops.interface M.index).top
  let i : I := (PermutationStabilizerTransport.pointEquiv M.points M.conjugator).symm 0
  let e := PermutationStabilizerTransport.stabilizerEquiv
    F.top.range T M.points M.conjugator M.matched 0
  let f := degreeFourPairPointLocalMap block P hr hD F i
  have hf : Function.Surjective f :=
    degreeFourZeroCoreTopStabilizerLocalMap_surjective block P hr hD (F.frame (i, 0))
  let q := F.descendedPointLocalMap hker i f hf (degreeFourLocalTarget_eligible block P hr)
  have hq : Function.Surjective q :=
    F.descendedPointLocalMap_surjective hker i f hf (degreeFourLocalTarget_eligible block P hr)
  exact DegreeFourEightTopEligibility.no_eligible_quotient M.index hj
    (q.comp e.symm.toMonoidHom)
    (degreeFourZeroCoreTopStabilizerLocalTarget_card block P hr)
    (hq.comp e.symm.surjective)

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
