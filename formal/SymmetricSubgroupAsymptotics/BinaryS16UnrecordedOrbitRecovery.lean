import SymmetricSubgroupAsymptotics.BinaryS16UnrecordedC2V4Recovery
import SymmetricSubgroupAsymptotics.BinaryS16UnrecordedOrbitD8E8
import SymmetricSubgroupAsymptotics.BinaryS16UnrecordedCyclicFourRecovery

/-!
# Recovering every unrecorded S16 source orbit from the physical target

The five unrecorded constructors are one-cell routes and were checked in
separate bounded modules.  The two carrier constructors always emit a mixed
record.  This file is the small exhaustive dispatcher.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryS16UnrecordedOrbitRecovery

open SymmetricSubgroupAsymptotics
open BinaryS16CanonicalCarrierProfile
open BinaryS16CanonicalMixedBlockTable
open BinaryS16DirectCertifiedOrbitProfile
open BinaryS16DirectFixedSupportClosure
open BinaryS16DirectPhysicalEncoding
open BinaryS16DirectPhysicalTarget
open BinaryS16UnrecordedC2V4Recovery
open BinaryS16UnrecordedOrbitD8E8
open BinaryS16UnrecordedCyclicFourRecovery

variable {N : ℕ} (C : SupportIndex N)

/-- Every source orbit omitted from the mixed table is a literal orbit of the
explicit relabelled raw target subgroup. -/
theorem unrecorded_sourceOrbit_is_targetOrbit
    (A : BinaryS16DirectPhysicalTarget.Actual C)
    (o : OrbitProfileFromOrbits.Orbit (subgroup C A))
    (hunrecorded : recordAt (subgroup C A) (residualSector C A) o = none) :
    ∃ z : Fin (2 * N),
      MulAction.orbit (targetSubgroup C A) z = o.orbit := by
  generalize hp : profile (subgroup C A) (residualSector C A) o = P at hunrecorded
  cases P with
  | c2 e he =>
      exact c2_sourceOrbit_is_targetOrbit C A o e he hp
  | v4 e he =>
      exact v4_sourceOrbit_is_targetOrbit C A o e he hp
  | d8 e he =>
      exact d8_sourceOrbit_is_targetOrbit C A o hp
  | e8 e he =>
      exact e8_sourceOrbit_is_targetOrbit C A o hp
  | cyclicFour W hpoint R =>
      exact cyclicFour_sourceOrbit_is_targetOrbit C A o W hpoint R hp
  | carrier8 W hpoint R =>
      exact False.elim
        (carrier8_profile_not_unrecorded C A o W hpoint R hp hunrecorded)
  | carrier16 W hpoint R =>
      exact False.elim
        (carrier16_profile_not_unrecorded C A o W hpoint R hp hunrecorded)

end SymmetricSubgroupAsymptotics.BinaryS16UnrecordedOrbitRecovery

end
