import SymmetricSubgroupAsymptotics.BinaryMarkedGoursatPeel
import SymmetricSubgroupAsymptotics.PrimeNormalHeadOrder
import SymmetricSubgroupAsymptotics.PrimeRelativeRadicalDerivedHead

/-! Uniform upper capacities for every actual original normal axis.
One original evaluation-kernel containment and one original derived-normal
rank bound supply both m and a2. The axis order is retained literally;
no stored profile, finite normal enumeration or quotient replacement occurs. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace BinaryMarkedGoursatPeel

open FullSubdirectGoursat

variable {A : Type} [Group A] [Finite A] (N : NormalAxis A)

/-- The maximum on N ∩ A′ is bounded by the order of the original N,
with conjugation still taken under the whole original A. -/
theorem derivedHead_le_orderLog : derivedHead N ≤ orderLog N :=
  (primeNormalHeadMax_mono 2
    (show N.1 ⊓ commutator A ≤ N.1 from inf_le_left)).trans
      (primeNormalHeadMax_le_log_card 2 N.1)

/-- Restricting the family of eligible original normals bounds the axis
maximum by the complete original derived-normal rank. -/
theorem derivedHead_le_derivedNormalRank :
    derivedHead N ≤ primeDerivedNormalRank 2 A :=
  primeNormalHeadMax_mono 2
    (show N.1 ⊓ commutator A ≤ commutator A from inf_le_right)

/-- Both actual capacities fit the same coarse box min(log₂|N|, r).
The evaluation-kernel hypothesis is a property of A, not of each axis;
it ensures that the actual relative radical belongs to the same maximum. -/
theorem maxHead_le_min_orderLog_rank (r : ℕ)
    (hA : (primeAbelianizationGroupMap 2 A).ker ≤ commutator A)
    (hr : primeDerivedNormalRank 2 A ≤ r) :
    max (derivedHead N) (radicalHead N) ≤ min (orderLog N) r := by
  have hradical : radicalHead N ≤ derivedHead N :=
    primeRelativeRadical_head_le_axis_max_of_evaluation_kernel_le 2 N.1 hA
  rw [max_eq_left hradical]
  exact le_min (derivedHead_le_orderLog N)
    ((derivedHead_le_derivedNormalRank N).trans hr)

end BinaryMarkedGoursatPeel
end SymmetricSubgroupAsymptotics
