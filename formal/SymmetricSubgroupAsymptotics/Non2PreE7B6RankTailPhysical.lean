import SymmetricSubgroupAsymptotics.FusionPhysicalSummedSource
import SymmetricSubgroupAsymptotics.Non2PreE7B6RankTailInstance

/-!
# Physical B6 row with the binary rank tail retained

This is the first consumer of the summed-source physical transfer.  The
cold and hot source terms remain correlated exactly as in the B6 certificate;
the original action normalizer and exact benchmark are installed only after
that sum has been bounded.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

namespace PreE7B6RankTailCertificate

variable {w : ℕ} {i : PreE7NonPairActionClass w}
  (C : PreE7B6RankTailCertificate w i)

/-- The B6 certificate gives a physical original-weight row without a
pointwise-in-source envelope.  This is the form to be inserted into the
special-moment branch of the global physical cover. -/
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
              (2 : ℝ) ^ ((4 / 3 : ℝ) * b) *
              (subgroupCount b : ℝ) +
          C.normalCount * ((Nat.factorial b : ℕ) : ℝ) ^ 16 *
            ((2 : ℝ) ^
                (-((b6RankTailExponent b : ℝ) * (13 / 50) * b)) *
              (subgroupCount
                (b + 2 * b6RankTailExponent b) : ℝ))) := by
  exact fusionPhysical_summedSource_normalized_bound
    (preE7NonPairAction w i) P hP _ (C.summed b P)

end PreE7B6RankTailCertificate

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
