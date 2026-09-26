import SymmetricSubgroupAsymptotics.BinaryCarrierRadicalSaturation16T1082
import SymmetricSubgroupAsymptotics.BinaryCarrierFormKernelExact16T1082
import SymmetricSubgroupAsymptotics.BinaryCarrierRadicalSaturation16T1083
import SymmetricSubgroupAsymptotics.BinaryCarrierFormKernelExact16T1083
import SymmetricSubgroupAsymptotics.BinaryCarrierRadicalSaturation16T1084
import SymmetricSubgroupAsymptotics.BinaryCarrierFormKernelExact16T1084
import SymmetricSubgroupAsymptotics.BinaryCarrierRadicalSaturation16T1547
import SymmetricSubgroupAsymptotics.BinaryCarrierFormKernelExact16T1547
import SymmetricSubgroupAsymptotics.BinaryCarrierProperIntersection16
import SymmetricSubgroupAsymptotics.PrimeDerivedCrossingCommutator
import SymmetricSubgroupAsymptotics.PrimeDerivedIntersectionExactHead
import SymmetricSubgroupAsymptotics.PrimeDerivedCrossingQuotient

/-! Every crossing original normal in the four pair-family masters has
exact mixed commutator and relative radical equal to its derived
intersection. Its relative head is its one- or two-dimensional actual
quotient image. Exact quotient invariants concern the same original N;
radical containment is derived from checked saturation, not assumed. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics

namespace BinaryCarrierCrossing16T1082

abbrev Original := BinaryCarrierDerivedOrder16T1082.Original
private abbrev kernelIdentity := BinaryCarrierDerived16T1082.evaluationKernel_eq_commutator

theorem radical_le_intersection (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) :
    primeRelativeRadical 2 (commutator Original) ≤ N ⊓ commutator Original :=
  BinaryCarrierRadicalSaturation16T1082.certificate.radical_le_intersection_of_not_le
    N hnotND (BinaryCarrierProperIntersection16T1082.normal_le_radical_of_intersection_le_radical N)

theorem mixed_eq_intersection (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    ⁅N, (⊤ : Subgroup Original)⁆ = N ⊓ commutator Original := by
  apply derivedCrossing_mixedCommutator_eq_of_normal_comparability 2 kernelIdentity
    BinaryCarrierFormTransport16T1082.actual_form_ker_inf_eq_bot_of_independent
    BinaryCarrierExactOrder16T1082.original_isPGroup
  · rw [BinaryCarrierDerivedRadical16T1082.relative_character_rank]
    decide
  · exact BinaryCarrierRadicalSaturation16T1082.normal_comparable
  · exact hnotND
  · exact hnotDN

theorem relative_radical_eq_intersection (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    primeRelativeRadical 2 N = N ⊓ commutator Original :=
  primeRelativeRadical_eq_intersection_of_mixed_eq 2 kernelIdentity.le N
    (mixed_eq_intersection N hnotND hnotDN)

theorem relative_head_eq_image (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) =
      Module.finrank (ZMod 2) (primeDerivedImage 2 N) :=
  primeRelativeCharacters_finrank_eq_image_of_mixed_eq 2 kernelIdentity N
    (mixed_eq_intersection N hnotND hnotDN)

theorem exact_quotient_invariants (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    1 ≤ Module.finrank (ZMod 2) (primeDerivedImage 2 N) ∧
      Module.finrank (ZMod 2) (primeDerivedImage 2 N) ≤ 2 ∧
      2 * Nat.card ↥(N ⊓ commutator Original) = Nat.card (commutator Original) ∧
      Nat.card (Subgroup.center (Original ⧸ N)) =
        2 ^ (3 - Module.finrank (ZMod 2) (primeDerivedImage 2 N)) ∧
      Nat.card (commutator (Original ⧸ N)) = 2 :=
  derivedCrossing_exact_quotient_invariants 2 kernelIdentity
    BinaryCarrierExactOrder16T1082.original_isPGroup
    BinaryCarrierFormTransport16T1082.actual_form_ker_inf_eq_bot_of_independent 2
    BinaryCarrierFormKernelExact16T1082.actual_form_finrank_ker_eq_two
    N hnotND hnotDN (radical_le_intersection N hnotND)

theorem relative_head_le_two (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) ≤ 2 := by
  rw [relative_head_eq_image N hnotND hnotDN]
  exact (exact_quotient_invariants N hnotND hnotDN).2.1

end BinaryCarrierCrossing16T1082

namespace BinaryCarrierCrossing16T1083

abbrev Original := BinaryCarrierDerivedOrder16T1083.Original
private abbrev kernelIdentity := BinaryCarrierDerived16T1083.evaluationKernel_eq_commutator

theorem radical_le_intersection (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) :
    primeRelativeRadical 2 (commutator Original) ≤ N ⊓ commutator Original :=
  BinaryCarrierRadicalSaturation16T1083.certificate.radical_le_intersection_of_not_le
    N hnotND (BinaryCarrierProperIntersection16T1083.normal_le_radical_of_intersection_le_radical N)

theorem mixed_eq_intersection (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    ⁅N, (⊤ : Subgroup Original)⁆ = N ⊓ commutator Original := by
  apply derivedCrossing_mixedCommutator_eq_of_normal_comparability 2 kernelIdentity
    BinaryCarrierFormTransport16T1083.actual_form_ker_inf_eq_bot_of_independent
    BinaryCarrierExactOrder16T1083.original_isPGroup
  · rw [BinaryCarrierDerivedRadical16T1083.relative_character_rank]
    decide
  · exact BinaryCarrierRadicalSaturation16T1083.normal_comparable
  · exact hnotND
  · exact hnotDN

theorem relative_radical_eq_intersection (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    primeRelativeRadical 2 N = N ⊓ commutator Original :=
  primeRelativeRadical_eq_intersection_of_mixed_eq 2 kernelIdentity.le N
    (mixed_eq_intersection N hnotND hnotDN)

theorem relative_head_eq_image (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) =
      Module.finrank (ZMod 2) (primeDerivedImage 2 N) :=
  primeRelativeCharacters_finrank_eq_image_of_mixed_eq 2 kernelIdentity N
    (mixed_eq_intersection N hnotND hnotDN)

theorem exact_quotient_invariants (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    1 ≤ Module.finrank (ZMod 2) (primeDerivedImage 2 N) ∧
      Module.finrank (ZMod 2) (primeDerivedImage 2 N) ≤ 2 ∧
      2 * Nat.card ↥(N ⊓ commutator Original) = Nat.card (commutator Original) ∧
      Nat.card (Subgroup.center (Original ⧸ N)) =
        2 ^ (3 - Module.finrank (ZMod 2) (primeDerivedImage 2 N)) ∧
      Nat.card (commutator (Original ⧸ N)) = 2 :=
  derivedCrossing_exact_quotient_invariants 2 kernelIdentity
    BinaryCarrierExactOrder16T1083.original_isPGroup
    BinaryCarrierFormTransport16T1083.actual_form_ker_inf_eq_bot_of_independent 2
    BinaryCarrierFormKernelExact16T1083.actual_form_finrank_ker_eq_two
    N hnotND hnotDN (radical_le_intersection N hnotND)

theorem relative_head_le_two (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) ≤ 2 := by
  rw [relative_head_eq_image N hnotND hnotDN]
  exact (exact_quotient_invariants N hnotND hnotDN).2.1

end BinaryCarrierCrossing16T1083

namespace BinaryCarrierCrossing16T1084

abbrev Original := BinaryCarrierDerivedOrder16T1084.Original
private abbrev kernelIdentity := BinaryCarrierDerived16T1084.evaluationKernel_eq_commutator

theorem radical_le_intersection (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) :
    primeRelativeRadical 2 (commutator Original) ≤ N ⊓ commutator Original :=
  BinaryCarrierRadicalSaturation16T1084.certificate.radical_le_intersection_of_not_le
    N hnotND (BinaryCarrierProperIntersection16T1084.normal_le_radical_of_intersection_le_radical N)

theorem mixed_eq_intersection (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    ⁅N, (⊤ : Subgroup Original)⁆ = N ⊓ commutator Original := by
  apply derivedCrossing_mixedCommutator_eq_of_normal_comparability 2 kernelIdentity
    BinaryCarrierFormTransport16T1084.actual_form_ker_inf_eq_bot_of_independent
    BinaryCarrierExactOrder16T1084.original_isPGroup
  · rw [BinaryCarrierDerivedRadical16T1084.relative_character_rank]
    decide
  · exact BinaryCarrierRadicalSaturation16T1084.normal_comparable
  · exact hnotND
  · exact hnotDN

theorem relative_radical_eq_intersection (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    primeRelativeRadical 2 N = N ⊓ commutator Original :=
  primeRelativeRadical_eq_intersection_of_mixed_eq 2 kernelIdentity.le N
    (mixed_eq_intersection N hnotND hnotDN)

theorem relative_head_eq_image (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) =
      Module.finrank (ZMod 2) (primeDerivedImage 2 N) :=
  primeRelativeCharacters_finrank_eq_image_of_mixed_eq 2 kernelIdentity N
    (mixed_eq_intersection N hnotND hnotDN)

theorem exact_quotient_invariants (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    1 ≤ Module.finrank (ZMod 2) (primeDerivedImage 2 N) ∧
      Module.finrank (ZMod 2) (primeDerivedImage 2 N) ≤ 2 ∧
      2 * Nat.card ↥(N ⊓ commutator Original) = Nat.card (commutator Original) ∧
      Nat.card (Subgroup.center (Original ⧸ N)) =
        2 ^ (3 - Module.finrank (ZMod 2) (primeDerivedImage 2 N)) ∧
      Nat.card (commutator (Original ⧸ N)) = 2 :=
  derivedCrossing_exact_quotient_invariants 2 kernelIdentity
    BinaryCarrierExactOrder16T1084.original_isPGroup
    BinaryCarrierFormTransport16T1084.actual_form_ker_inf_eq_bot_of_independent 2
    BinaryCarrierFormKernelExact16T1084.actual_form_finrank_ker_eq_two
    N hnotND hnotDN (radical_le_intersection N hnotND)

theorem relative_head_le_two (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) ≤ 2 := by
  rw [relative_head_eq_image N hnotND hnotDN]
  exact (exact_quotient_invariants N hnotND hnotDN).2.1

end BinaryCarrierCrossing16T1084

namespace BinaryCarrierCrossing16T1547

abbrev Original := BinaryCarrierDerivedOrder16T1547.Original
private abbrev kernelIdentity := BinaryCarrierDerived16T1547.evaluationKernel_eq_commutator

theorem radical_le_intersection (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) :
    primeRelativeRadical 2 (commutator Original) ≤ N ⊓ commutator Original :=
  BinaryCarrierRadicalSaturation16T1547.certificate.radical_le_intersection_of_not_le
    N hnotND (BinaryCarrierProperIntersection16T1547.normal_le_radical_of_intersection_le_radical N)

theorem mixed_eq_intersection (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    ⁅N, (⊤ : Subgroup Original)⁆ = N ⊓ commutator Original := by
  apply derivedCrossing_mixedCommutator_eq_of_normal_comparability 2 kernelIdentity
    BinaryCarrierFormTransport16T1547.actual_form_ker_inf_eq_bot_of_independent
    BinaryCarrierExactOrder16T1547.original_isPGroup
  · rw [BinaryCarrierDerivedRadical16T1547.relative_character_rank]
    decide
  · exact BinaryCarrierRadicalSaturation16T1547.normal_comparable
  · exact hnotND
  · exact hnotDN

theorem relative_radical_eq_intersection (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    primeRelativeRadical 2 N = N ⊓ commutator Original :=
  primeRelativeRadical_eq_intersection_of_mixed_eq 2 kernelIdentity.le N
    (mixed_eq_intersection N hnotND hnotDN)

theorem relative_head_eq_image (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) =
      Module.finrank (ZMod 2) (primeDerivedImage 2 N) :=
  primeRelativeCharacters_finrank_eq_image_of_mixed_eq 2 kernelIdentity N
    (mixed_eq_intersection N hnotND hnotDN)

theorem exact_quotient_invariants (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    1 ≤ Module.finrank (ZMod 2) (primeDerivedImage 2 N) ∧
      Module.finrank (ZMod 2) (primeDerivedImage 2 N) ≤ 2 ∧
      2 * Nat.card ↥(N ⊓ commutator Original) = Nat.card (commutator Original) ∧
      Nat.card (Subgroup.center (Original ⧸ N)) =
        2 ^ (3 - Module.finrank (ZMod 2) (primeDerivedImage 2 N)) ∧
      Nat.card (commutator (Original ⧸ N)) = 2 :=
  derivedCrossing_exact_quotient_invariants 2 kernelIdentity
    BinaryCarrierExactOrder16T1547.original_isPGroup
    BinaryCarrierFormTransport16T1547.actual_form_ker_inf_eq_bot_of_independent 2
    BinaryCarrierFormKernelExact16T1547.actual_form_finrank_ker_eq_two
    N hnotND hnotDN (radical_le_intersection N hnotND)

theorem relative_head_le_two (N : Subgroup Original) [N.Normal]
    (hnotND : ¬N ≤ commutator Original) (hnotDN : ¬commutator Original ≤ N) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) ≤ 2 := by
  rw [relative_head_eq_image N hnotND hnotDN]
  exact (exact_quotient_invariants N hnotND hnotDN).2.1

end BinaryCarrierCrossing16T1547

end SymmetricSubgroupAsymptotics
