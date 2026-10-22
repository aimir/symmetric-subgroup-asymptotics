import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4PointTypeFaithfulness
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDPolarFamilyCardinality
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDSubgroupOuterCardinality
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDProjectiveRealization
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! Actual outer bounds on the original D4 model. The POINT-type
stabilizer has index three; its two maximal-space types are allowed to
interchange. Its reconstructed faithful point/plane action supplies the
whole polar realization, so no recognition or lift premise remains.
The characteristic-two centre and isometry index give the sharper factor.
The logarithmic consumer is separate from these cardinality statements. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDFourOuterCardinality
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPlaneFamilyAction
open CFSGOrthogonalDIndexTrialityD4ResidualSpace CFSGOrthogonalDIndexQuadraticForm
open PrimitiveSocleRawStructure
variable (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (elementaryProjective K 4)]

theorem pointTypeStabilizer_card_le_quadratic_mul_field
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    Nat.card (naturalPointTypeStabilizer K p) ≤
      Nat.card (quadraticPreserving K 4) * Nat.card (K ≃+* K) := by
  apply CFSGOrthogonalDPolarFamilyCardinality.point_family_card_le_quadratic_mul_field K 0
    (fun f => pointTypeAction K p f) (fun f => singularActionHom K p 0 f.val)
    (pointTypeAction_injective K p)
  · exact fun f U P => pointTypeAction_incidence K p f U P
  · exact fun f U V => pointTypeAction_preserves_orthogonal K p f U V

theorem outer_card_le_twentyFour_field (p : ℕ) [Fact p.Prime] [CharP K p] :
    Nat.card (Outer (elementaryProjective K 4)) ≤ 24 * Nat.card (K ≃+* K) := by
  simpa using CFSGOrthogonalDSubgroupOuterCardinality.outer_card_le_eight_index_field K 0
    (naturalPointTypeStabilizer K p) 3 (naturalPointTypeStabilizer_index_le_three K p)
    (pointTypeStabilizer_card_le_quadratic_mul_field K p)

theorem outer_card_le_six_field [CharP K 2] :
    Nat.card (Outer (elementaryProjective K 4)) ≤ 6 * Nat.card (K ≃+* K) := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  simpa using CFSGOrthogonalDSubgroupOuterCardinality.outer_card_le_two_index_field K 0
    (naturalPointTypeStabilizer K 2) 3 (naturalPointTypeStabilizer_index_le_three K 2)
    (pointTypeStabilizer_card_le_quadratic_mul_field K 2)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDFourOuterCardinality

namespace SymmetricSubgroupAsymptotics.CFSGReduction
open CFSGOrthogonalDSerreMatrices PrimitiveSocleRawStructure

theorem typeD_four_outer_card_le (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.D 4 q)] :
    Nat.card (Outer (CFSG.Models.D 4 q)) ≤ 24 * Nat.card (q.Field ≃+* q.Field) := by
  let e := serreProjectiveEquivElementaryProjective q.Field 0
  letI : IsSimpleGroup (elementaryProjective q.Field 4) := e.symm.isSimpleGroup
  rw [outer_card_congr e]
  exact CFSGOrthogonalDFourOuterCardinality.outer_card_le_twentyFour_field q.Field q.prime

theorem typeD_four_binary_outer_card_le (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.D 4 q)] (hq : q.prime = 2) :
    Nat.card (Outer (CFSG.Models.D 4 q)) ≤ 6 * Nat.card (q.Field ≃+* q.Field) := by
  letI : CharP q.Field 2 := by simpa only [hq] using (inferInstance : CharP q.Field q.prime)
  let e := serreProjectiveEquivElementaryProjective q.Field 0
  letI : IsSimpleGroup (elementaryProjective q.Field 4) := e.symm.isSimpleGroup
  rw [outer_card_congr e]
  exact CFSGOrthogonalDFourOuterCardinality.outer_card_le_six_field q.Field

end SymmetricSubgroupAsymptotics.CFSGReduction
