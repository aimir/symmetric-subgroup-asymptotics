import SymmetricSubgroupAsymptotics.BinaryCarrierWordEnergy
import SymmetricSubgroupAsymptotics.JointCapacityRowEnvelope

/-! Install actual history certificates from proved upper bounds on their
invariants. A finite producer may certify upper boxes instead of exact
radical/normal-head values, but must bind each box to its original row.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryCarrierWord

open BinaryCarrierCone JointCapacityRow

/-- Numerical domination of upper rows transfers to the same actual rows.
All six actual inequalities remain explicit. This does not identify a
stored profile label with an original normal subgroup or prove coverage. -/
def CertifiedHistoryRows.of_upperRows
    (w : List Factor) (T : ℝ)
    (upper : History w → Fin w.length → JointCapacityRow)
    (hupper : ∀ h i, BoundedBy (rows h i) (upper h i))
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
    (symmetricSupport_mono (hupper h a) (hupper h i)).trans (hpair h a i hai)
  total_mass := hmass

end SymmetricSubgroupAsymptotics.BinaryCarrierWord
