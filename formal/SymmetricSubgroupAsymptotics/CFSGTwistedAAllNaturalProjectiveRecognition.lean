import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalProjectiveRecognition
import SymmetricSubgroupAsymptotics.CFSGTwistedA2DerivedFaithfulness

/-! Original twisted-A natural projective correspondence over its ENTIRE
literal admissible parameter range. This concludes source faithfulness
onto the actual derived image, not recognition as a full unitary group.
The original source simplicity is used only by projective descent. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices

theorem derived_natural_projective_nontrivial_of_admissible
    (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    (hq : r = 2 → q.order ≠ 2) :
    Nontrivial ((twistedDerivedAction r q).range ⧸
      Subgroup.center (twistedDerivedAction r q).range) := by
  by_cases he : r = 2
  · subst r
    have hq2 : 2 ≤ q.order := q.prime_isPrime.two_le.trans
      (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
    exact CFSGTwistedA2HighestRootUnits.derived_projective_nontrivial q (by
      have := hq rfl
      omega)
  · exact derived_natural_projective_nontrivial_of_three_le r (by omega) q

def twistedA_natural_projective_equiv_of_admissible
    (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    (hq : r = 2 → q.order ≠ 2)
    [IsSimpleGroup (CFSG.Models.TwistedA r q)] :
    CFSG.Models.TwistedA r q ≃*
      ((twistedDerivedAction r q).range ⧸
        Subgroup.center (twistedDerivedAction r q).range) := by
  letI := derived_natural_projective_nontrivial_of_admissible r hr q hq
  exact CFSGSimpleProjectiveDescent.projectiveEquivOfSimple
    (twistedDerivedAction r q).rangeRestrict (twistedDerivedAction r q).rangeRestrict_surjective

theorem twistedA_natural_projective_map_injective_of_admissible
    (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    (hq : r = 2 → q.order ≠ 2)
    [IsSimpleGroup (CFSG.Models.TwistedA r q)] :
    Function.Injective (CFSGSimpleProjectiveDescent.projectiveMap
      (twistedDerivedAction r q).rangeRestrict
        (twistedDerivedAction r q).rangeRestrict_surjective) := by
  letI := derived_natural_projective_nontrivial_of_admissible r hr q hq
  exact CFSGSimpleProjectiveDescent.projectiveMap_injective _ _

end SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
