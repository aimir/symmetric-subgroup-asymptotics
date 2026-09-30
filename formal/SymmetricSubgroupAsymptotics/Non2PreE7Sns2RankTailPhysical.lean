import SymmetricSubgroupAsymptotics.FusionPhysicalSummedSource
import SymmetricSubgroupAsymptotics.Non2PreE7Sns2RankTailInstance

/-!
# Physical SNS2 row with the weighted binary rank tail retained

The source weight `2^(ℓ d₂(J))` remains inside the sum over literal complete
sources.  Physical pointing is applied only after that weighted sum, with
the original action and original normalizer retained exactly once.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

namespace PreE7Sns2RankTailCertificate

variable {w : ℕ} {i : PreE7NonPairActionClass w}
  (C : PreE7Sns2RankTailCertificate w i)

/-- The SNS2 certificate gives its exact physical original-weight row. -/
theorem physical_normalized_bound
    (b : ℕ)
    (P : Subgroup
      (preE7NonPairAction w i × Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural (preE7NonPairAction w i) P) :
    (Nat.card (FusionOrbitFamily (preE7NonPairAction w i)
        (FusionAcceptedOrbitPredicate (preE7NonPairAction w i) P)) : ℝ) /
        exactBenchmark (b + w) ≤
      growingQuotientNormalizedPointing b w
          (Nat.card (Subgroup.normalizer
            (preE7NonPairAction w i :
              Set (Equiv.Perm (Fin w)))) : ℝ) *
        (C.normalCount * C.outerFactor b *
              (2 : ℝ) ^
                ((C.quotientRank : ℝ) * ((51 / 200) * b)) *
              (subgroupCount b : ℝ) +
          C.normalCount * C.outerFactor b *
            ((2 : ℝ) ^
                (-(((sns2RankTailTilt b C.quotientRank : ℝ) -
                    C.quotientRank) * (51 / 200) * b)) *
              (subgroupCount
                (b + 2 * sns2RankTailTilt b C.quotientRank) : ℝ))) := by
  exact fusionPhysical_summedSource_normalized_bound
    (preE7NonPairAction w i) P hP _ (C.summed b P)

end PreE7Sns2RankTailCertificate

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
