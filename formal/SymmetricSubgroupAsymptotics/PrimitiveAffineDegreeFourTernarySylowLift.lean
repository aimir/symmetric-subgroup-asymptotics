import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourComplementRank
import SymmetricSubgroupAsymptotics.SylowNormalQuotientLift

/-! Every original Sylow-three subgroup sees the full local ternary core
at every physical block. This lifts the correlated quotient core through
the original binary translation kernel, with its exact original action. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (S : Sylow 3 (preE7NonPairAction w U))

abbrev degreeFourSylowCore : Subgroup S :=
  SylowNormalQuotientLift.preimage (QuotientGroup.mk' (E block P))
    (degreeFourTernaryCore block P) S

abbrev degreeFourSylowCoreProjection :
    degreeFourSylowCore block P S →* degreeFourTernaryCore block P :=
  SylowNormalQuotientLift.projection (QuotientGroup.mk' (E block P))
    (degreeFourTernaryCore block P) S

theorem degreeFourSylowCoreProjection_surjective (hr : Nat.card block.Fibre = 4) :
    Function.Surjective (degreeFourSylowCoreProjection block P S) :=
  SylowNormalQuotientLift.projection_surjective (QuotientGroup.mk' (E block P))
    (QuotientGroup.mk'_surjective (E block P)) (degreeFourTernaryCore block P)
    (degreeFourTernaryCore_isPGroup block P hr) S

def degreeFourSylowCoreCoordinate (i : block.Points) :
    degreeFourSylowCore block P S →* (degreeFourLocalBinarySign block P).ker :=
  (degreeFourTernaryCoordinate block P i).comp (degreeFourSylowCoreProjection block P S)

theorem degreeFourSylowCoreCoordinate_surjective
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P ≠ ⊥)
    (i : block.Points) : Function.Surjective (degreeFourSylowCoreCoordinate block P S i) :=
  (degreeFourTernaryCoordinate_surjective block P hr hD i).comp
    (degreeFourSylowCoreProjection_surjective block P S hr)

/-- These are elements of the original block kernel, so their orbits
remain inside the same original physical fibre. -/
theorem degreeFourSylowCore_fixes_blocks
    (a : degreeFourSylowCore block P S) (i : block.Points) :
    (((a.1 : S) : preE7NonPairAction w U) • i) = i := by
  have ha := degreeFourTernaryCore_le_blockKernel block P
    (degreeFourSylowCoreProjection block P S a).2
  have he : block.topMap.rangeRestrict ((a.1 : S) : preE7NonPairAction w U) = 1 := ha
  exact congrArg (fun t : block.Top => t • i) he

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
