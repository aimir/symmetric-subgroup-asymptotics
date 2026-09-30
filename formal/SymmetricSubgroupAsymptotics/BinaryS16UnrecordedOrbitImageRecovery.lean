import SymmetricSubgroupAsymptotics.BinaryS16UnrecordedC2V4ImageRecovery
import SymmetricSubgroupAsymptotics.BinaryS16UnrecordedD8E8ImageRecovery
import SymmetricSubgroupAsymptotics.BinaryS16UnrecordedCyclicFourImageRecovery

/-!
# Complete action recovery on every unrecorded S16 source orbit

The five constructors which can be absent from the mixed block table are
one-cell routes.  Their branch theorems recover both the target orbit and its
complete restriction image.  The two positive carrier constructors always
write a mixed-table record, so the same seven-way certificate split gives
the unconditional unrecorded result below.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryS16UnrecordedOrbitImageRecovery

open SymmetricSubgroupAsymptotics
open BinaryS16CanonicalCarrierProfile
open BinaryS16CanonicalMixedBlockTable
open BinaryS16DirectCertifiedOrbitProfile
open BinaryS16DirectFixedSupportClosure
open BinaryS16DirectPhysicalEncoding
open BinaryS16DirectPhysicalTarget
open BinaryS16UnrecordedC2V4ImageRecovery
open BinaryS16UnrecordedD8E8ImageRecovery
open BinaryS16UnrecordedCyclicFourRecovery
open BinaryS16UnrecordedCyclicFourImageRecovery

variable {N : ℕ} (C : SupportIndex N)

/-- Every source orbit omitted from the mixed block table is a target orbit,
and after the proof-only cast between their equal point sets the target's
complete permutation image is exactly the original source image. -/
theorem unrecorded_sourceOrbitImage_is_targetOrbitImage
    (A : BinaryS16DirectPhysicalTarget.Actual C)
    (o : OrbitProfileFromOrbits.Orbit (subgroup C A))
    (hunrecorded : recordAt (subgroup C A) (residualSector C A) o = none) :
    ∃ p : OrbitProfileFromOrbits.Orbit (targetSubgroup C A),
      ∃ hp : p.orbit = o.orbit,
        relabelSubgroup (Equiv.setCongr hp)
            (OrbitProfileFromOrbits.orbitImage (targetSubgroup C A) p) =
          OrbitProfileFromOrbits.orbitImage (subgroup C A) o := by
  generalize hp : profile (subgroup C A) (residualSector C A) o = P at hunrecorded
  cases P with
  | c2 e he =>
      exact c2_sourceOrbitImage_is_targetOrbitImage C A o e he hp
  | v4 e he =>
      exact v4_sourceOrbitImage_is_targetOrbitImage C A o e he hp
  | d8 e he =>
      exact d8_sourceOrbitImage_is_targetOrbitImage C A o hp
  | e8 e he =>
      exact e8_sourceOrbitImage_is_targetOrbitImage C A o hp
  | cyclicFour W hpoint R =>
      exact cyclicFour_sourceOrbitImage_is_targetOrbitImage
        C A o W hpoint R hp
  | carrier8 W hpoint R =>
      exact False.elim
        (carrier8_profile_not_unrecorded C A o W hpoint R hp hunrecorded)
  | carrier16 W hpoint R =>
      exact False.elim
        (carrier16_profile_not_unrecorded C A o W hpoint R hp hunrecorded)

end SymmetricSubgroupAsymptotics.BinaryS16UnrecordedOrbitImageRecovery

end
