import SymmetricSubgroupAsymptotics.BinaryDegree16SplitFrontier
import SymmetricSubgroupAsymptotics.BinaryPhysicalPairParameters

/-!
# Even physical pair certificates enter the degree-sixteen direct recurrence

The complete pair registries produce a quotient-cover degree and a binary
cut degree.  When the former is even, their sum is an even prefix strictly
below sixteen.  This file packages the already proved original envelope and
same-source moments into the common `AcceptedEntry` interface.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryPhysicalPairCertificate

variable {U : Subgroup (Equiv.Perm (Fin 16))} {N : Subgroup U} [N.Normal]

/-- An even selected top cover makes the physical pair prefix a legal direct
marker.  No numerical envelope is reproved here: every field is inherited
from the original physical certificate. -/
def acceptedEntry16 (hU : IsPGroup 2 U)
    (C : BinaryPhysicalPairCertificate U N)
    (heven : Even C.localCertificate.coverDegree) :
    BinaryDegree16SplitFrontier.AcceptedEntry U N := by
  have hcover := Nat.two_mul_div_two_of_even heven
  refine {
    prefixDegree := C.prefixDegree
    markerHalf := C.localCertificate.coverDegree/2+C.localCertificate.cutDimension
    liftConstant := C.liftConstant
    gapParameter := C.gapParameter
    momentWeight := fun {b} J => C.momentWeight J
    prefix_eq_two_mul := ?_
    prefix_lt := ?_
    liftConstant_nonneg := C.liftConstant_nonneg
    gapParameter_pos := C.gapParameter_pos
    moment_le := ?_
    original_envelope := ?_ }
  · unfold prefixDegree
    omega
  · have hgap := C.certified_gap
    omega
  · intro b q
    exact C.prefixDegree_moment_le b q
  · intro b P J
    exact C.original_survivingEpiCount_le_localFactor_ambient (h := 8) hU P J

end SymmetricSubgroupAsymptotics.BinaryPhysicalPairCertificate
