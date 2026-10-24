import SymmetricSubgroupAsymptotics.SmallAffineJointTinyCertificates

/-! The two remaining literal-order arithmetic specializations of the
checked small-primary engine. The domain is the same exact divisor set;
there is no new finite group or permutation enumeration. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SmallAffineJointTinyMoreCertificates
open SmallAffineJointTinyCertificates

theorem seven_certificates : ∀ t ∈ topDegrees, ∃ q : Fin 8, Certificate 7 42 t q := by
  unfold Certificate
  decide +kernel

theorem nine_certificates : ∀ t ∈ topDegrees, ∃ q : Fin 8, Certificate 9 432 t q := by
  unfold Certificate
  decide +kernel

end SymmetricSubgroupAsymptotics.SmallAffineJointTinyMoreCertificates
