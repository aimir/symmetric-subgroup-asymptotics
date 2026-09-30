import SymmetricSubgroupAsymptotics.BinaryS16JointAxisRouting
import SymmetricSubgroupAsymptotics.BinaryCarrierCertifiedPositivity

/-!
# The complete certified canonical word for the S16 residual sector

The direct joint profile, its seven-branch axis router, and its exact numerical
sums assemble into one canonical certified word.  Positive direct old support
then supplies the producer's required noncritical cell without extra marking.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryS16JointCertifiedWord

open SymmetricSubgroupAsymptotics
open BinaryCarrierCanonicalCertifiedWord
open BinaryCarrierCertifiedPositivity
open BinaryCarrierDependentVariableWordProducer
open BinaryS16CanonicalCarrierProfile

variable {N : ℕ}
variable (H : Subgroup (Equiv.Perm (Fin (2 * N))))
variable (hH : ResidualSector H)

/-- The complete deterministic canonical word, with exact half-degree `N` and
exact direct old support. -/
def certifiedWord : CanonicalCertifiedWord
    (BinaryS16JointOrbitData.Points H hH)
    (BinaryS16JointOrbitData.action H hH) H
    (BinaryS16JointOrbitData.data H hH) N
    (BinaryS16JointOrbitData.oldSupport H hH) where
  parameter := fun q ↦ BinaryS16JointOrbitData.parameter H hH q.1
  oldSupport := fun q ↦ BinaryS16JointOrbitData.oldSupportAt H hH q.1
  certified := BinaryS16JointAxisRouting.axisRouting H hH
  parameter_sum := BinaryS16JointOrbitData.occurrence_parameter_sum H hH
  oldSupport_sum := BinaryS16JointOrbitData.occurrence_oldSupport_sum H hH

/-- Positive direct old support gives a positive canonical occurrence. -/
theorem certifiedWord_hasPositiveOccurrence
    (hpositive : 0 < BinaryS16JointOrbitData.oldSupport H hH) :
    (certifiedWord H hH).HasPositiveOccurrence :=
  canonicalCertifiedWord_hasPositiveOccurrence_of_Cold_pos
    (certifiedWord H hH) hpositive

/-- The direct positive branch is ready for the retained-bin producer, with
the original subgroup's complete correlated source preserved. -/
def routedWord
    (hpositive : 0 < BinaryS16JointOrbitData.oldSupport H hH) :
    RoutedWord N (BinaryS16JointOrbitData.oldSupport H hH) :=
  (certifiedWord H hH).routedWord
    (certifiedWord_hasPositiveOccurrence H hH hpositive)

end SymmetricSubgroupAsymptotics.BinaryS16JointCertifiedWord

end
