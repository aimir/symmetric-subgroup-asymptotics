import SymmetricSubgroupAsymptotics.PrimitiveAffineEightAffineLocalExclusions
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightNaturalLocalExclusions
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightSharedTops
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourPairFrameSource
import SymmetricSubgroupAsymptotics.PermutationStabilizerTransport

/-!
The four rejected entries of the fixed twenty-four-action alphabet are
excluded on the original degree-four frame. The local map is transported
from the actual stabilizer, at the inverse image of literal point zero.
No eligible-top classification or local-kernel census is assumed here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeFourEightTopEligibility

def Excluded (j : Fin 24) : Prop := j = 17 ∨ j = 19 ∨ j = 22 ∨ j = 23

/-- These are the four actual point-stabilizer obstructions, in the same
ordered literal family used by the checked paired-eight quotient socles. -/
theorem no_eligible_quotient (j : Fin 24) (hj : Excluded j)
    {Q : Type} [Group Q] [Finite Q]
    (f : MulAction.stabilizer (DegreeTwoPairedEightSharedTops.interface j).top
      (0 : Fin 8) →* Q)
    (hQ : Nat.card Q = 3 ∨ Nat.card Q = 6) :
    ¬ Function.Surjective f := by
  rcases hj with rfl | rfl | rfl | rfl
  · exact PrimitiveAffineDegreeTwoPairedEightAffineTops.Row18.no_eligible_pointStabilizer_quotient f hQ
  · exact PrimitiveAffineDegreeTwoPairedEightAffineTops.Row20.no_eligible_pointStabilizer_quotient f hQ
  · exact PrimitiveAffineEightNaturalLocalExclusions.row23_no_eligible_pointStabilizer_quotient Q f hQ
  · exact PrimitiveAffineEightNaturalLocalExclusions.row24_no_eligible_pointStabilizer_quotient Q f hQ

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
  (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- A literal match for the original zero-core top cannot select one of
the four excluded classes. Its actual local epimorphism gives the contradiction. -/
theorem original_match_not_excluded
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥)
    (j : Fin 24) (points : block.Points ≃ Fin 8) (g : Equiv.Perm (Fin 8))
    (matched : MulAut.conj g • relabelSubgroup points block.Top =
      (DegreeTwoPairedEightSharedTops.interface j).top) :
    ¬ Excluded j := by
  intro hj
  let T := (DegreeTwoPairedEightSharedTops.interface j).top
  let x := (PermutationStabilizerTransport.pointEquiv points g).symm 0
  let e := PermutationStabilizerTransport.stabilizerEquiv
    block.Top T points g matched 0
  let f := (degreeFourZeroCoreTopStabilizerLocalMap block P hr hD x).comp
    e.symm.toMonoidHom
  apply no_eligible_quotient j hj f
    (degreeFourZeroCoreTopStabilizerLocalTarget_card block P hr)
  exact (degreeFourZeroCoreTopStabilizerLocalMap_surjective block P hr hD x).comp
    e.symm.surjective

end DegreeFourEightTopEligibility
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
