import SymmetricSubgroupAsymptotics.BinaryCarrierWordEnergy
import SymmetricSubgroupAsymptotics.JointCapacityEffectiveEnvelope

/-! Install numerical history certificates using inclusion of the entire
coupled feasible polygon. All original factors, normal axes, individual
weights and physical mass identities remain unchanged. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryCarrierWord

open BinaryCarrierCone JointCapacityRow

/-- Effective row domination suffices for the same actual history.
This does not replace the original subgroup order by a smaller number;
the literal row is bounded through its complete feasible polygon. -/
def CertifiedHistoryRows.of_effectiveUpperRows
    (w : List Factor) (T : ℝ)
    (upper : History w → Fin w.length → JointCapacityRow)
    (hupper : ∀ h i, EffectivelyBoundedBy (rows h i) (upper h i))
    (color : History w → Fin w.length → Fin 6)
    (mass : History w → Fin w.length → ℝ)
    (hu : ∀ h i, 0 ≤ mass h i)
    (hk : ∀ h i, ((upper h i).k : ℝ) ≤ mass h i * alpha (color h i))
    (hb : ∀ h i, ((max (upper h i).m (upper h i).a₂ : ℕ) : ℝ) ≤
      mass h i * beta (color h i))
    (hpair : ∀ h a i, a < i → symmetricSupport (upper h a) (upper h i) ≤
      mass h a * mass h i * pairMatrix64 (color h a) (color h i) / 64)
    (hmass : ∀ h, ∑ i, mass h i = 4*T) : CertifiedHistoryRows w T where
  color := color
  mass := mass
  mass_nonneg := hu
  head_le h i := (Nat.cast_le.mpr (hupper h i).head).trans (hk h i)
  second_le h i := (Nat.cast_le.mpr (hupper h i).second).trans (hb h i)
  pair_le h a i hai :=
    (symmetricSupport_mono_effective (hupper h a) (hupper h i)).trans (hpair h a i hai)
  total_mass := hmass

end SymmetricSubgroupAsymptotics.BinaryCarrierWord
