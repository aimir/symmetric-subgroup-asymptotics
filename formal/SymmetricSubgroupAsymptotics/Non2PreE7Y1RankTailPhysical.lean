import SymmetricSubgroupAsymptotics.FusionPhysicalSummedSource
import SymmetricSubgroupAsymptotics.Non2PreE7Y1RankTailInstance

/-!
# Physical Y1 row with the index-three binary rank tail retained

The cold and hot complete-source terms remain correlated until after the
sum over literal sources.  Physical pointing then installs the original
width-eight action and its normalizer exactly once.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

namespace PreE7Y1RankTailCertificate

variable {w : ℕ} {i : PreE7NonPairActionClass w}
  (C : PreE7Y1RankTailCertificate w i)

/-- The Y1 certificate gives a physical original-weight row without a
pointwise-in-source envelope. -/
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
        (C.coldConstant * (1 + b) *
              (2 : ℝ) ^ ((153 / 200 : ℝ) * b) *
              (subgroupCount b : ℝ) +
          C.normalCount * ((Nat.factorial b : ℕ) : ℝ) ^ 16 *
            ((Nat.factorial b : ℝ) *
              ((2 : ℝ) ^
                  (-((rankTail51Tilt b : ℝ) * (51 / 200) * b)) *
                (subgroupCount
                  (b + 2 * rankTail51Tilt b) : ℝ)))) := by
  exact fusionPhysical_summedSource_normalized_bound
    (preE7NonPairAction w i) P hP _ (C.summed b P)

end PreE7Y1RankTailCertificate

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
