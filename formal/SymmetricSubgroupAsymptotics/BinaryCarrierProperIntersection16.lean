import SymmetricSubgroupAsymptotics.BinaryCarrierExactOrders16
import SymmetricSubgroupAsymptotics.PrimeDerivedProperIntersection
import SymmetricSubgroupAsymptotics.PrimeDerivedIntersectionImage
import Lean.Elab.Tactic.Omega

/-! Uniform bounds on every original normal not containing G′ in the five
literal masters. Actual invariant derived characters supply the constraints;
no individual normal enumeration or profile assumption is required. Small
intersections inside the actual relative radical force the whole normal
into that radical. The remaining B-character power tests are still needed. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

namespace BinaryCarrierProperIntersection16T1082

abbrev Original := BinaryCarrierDerivedOrder16T1082.Original
private abbrev kernelIdentity := BinaryCarrierDerived16T1082.evaluationKernel_eq_commutator

theorem image_finrank_le_two (N : Subgroup Original) [N.Normal]
    (hN : ¬commutator Original ≤ N) :
    Module.finrank (ZMod 2) (primeDerivedImage 2 N) ≤ 2 :=
  primeDerivedImage_finrank_le_of_proper_intersection 2 kernelIdentity
    BinaryCarrierExactOrder16T1082.original_isPGroup 2
    BinaryCarrierFormTransport16T1082.actual_form_finrank_ker_le_two N hN

theorem quotient_log_le_two (N : Subgroup Original) [N.Normal]
    (hN : ¬commutator Original ≤ N) :
    Nat.log 2 (Nat.card (normalChainQuotient (N ⊓ commutator Original) N)) ≤ 2 := by
  rw [derivedIntersectionQuotient_log_card_eq_image 2 kernelIdentity N]
  exact image_finrank_le_two N hN

theorem card_le_4_mul_intersection (N : Subgroup Original) [N.Normal]
    (hN : ¬commutator Original ≤ N) :
    Nat.card N ≤ 4 * Nat.card ↥(N ⊓ commutator Original) :=
  normal_card_le_pow_mul_derivedIntersection 2 kernelIdentity N 2
    (image_finrank_le_two N hN)

theorem normal_le_derived_of_intersection_le_radical (N : Subgroup Original) [N.Normal]
    (hN : N ⊓ commutator Original ≤ primeRelativeRadical 2 (commutator Original)) :
    N ≤ commutator Original := by
  apply derivedCharactersVanishingOn_normal_le_commutator_of_two_le 2 kernelIdentity
    BinaryCarrierFormTransport16T1082.actual_form_ker_inf_eq_bot_of_independent
    (primeRelativeRadical 2 (commutator Original)) N hN
  rw [derivedCharactersVanishingOn_radical, finrank_top,
    BinaryCarrierDerivedRadical16T1082.relative_character_rank]
  decide

theorem normal_le_radical_of_intersection_le_radical (N : Subgroup Original) [N.Normal]
    (hN : N ⊓ commutator Original ≤ primeRelativeRadical 2 (commutator Original)) :
    N ≤ primeRelativeRadical 2 (commutator Original) := by
  have hd := normal_le_derived_of_intersection_le_radical N hN
  rwa [inf_eq_left.mpr hd] at hN

end BinaryCarrierProperIntersection16T1082

namespace BinaryCarrierProperIntersection16T1083

abbrev Original := BinaryCarrierDerivedOrder16T1083.Original
private abbrev kernelIdentity := BinaryCarrierDerived16T1083.evaluationKernel_eq_commutator

theorem image_finrank_le_two (N : Subgroup Original) [N.Normal]
    (hN : ¬commutator Original ≤ N) :
    Module.finrank (ZMod 2) (primeDerivedImage 2 N) ≤ 2 :=
  primeDerivedImage_finrank_le_of_proper_intersection 2 kernelIdentity
    BinaryCarrierExactOrder16T1083.original_isPGroup 2
    BinaryCarrierFormTransport16T1083.actual_form_finrank_ker_le_two N hN

theorem quotient_log_le_two (N : Subgroup Original) [N.Normal]
    (hN : ¬commutator Original ≤ N) :
    Nat.log 2 (Nat.card (normalChainQuotient (N ⊓ commutator Original) N)) ≤ 2 := by
  rw [derivedIntersectionQuotient_log_card_eq_image 2 kernelIdentity N]
  exact image_finrank_le_two N hN

theorem card_le_4_mul_intersection (N : Subgroup Original) [N.Normal]
    (hN : ¬commutator Original ≤ N) :
    Nat.card N ≤ 4 * Nat.card ↥(N ⊓ commutator Original) :=
  normal_card_le_pow_mul_derivedIntersection 2 kernelIdentity N 2
    (image_finrank_le_two N hN)

theorem normal_le_derived_of_intersection_le_radical (N : Subgroup Original) [N.Normal]
    (hN : N ⊓ commutator Original ≤ primeRelativeRadical 2 (commutator Original)) :
    N ≤ commutator Original := by
  apply derivedCharactersVanishingOn_normal_le_commutator_of_two_le 2 kernelIdentity
    BinaryCarrierFormTransport16T1083.actual_form_ker_inf_eq_bot_of_independent
    (primeRelativeRadical 2 (commutator Original)) N hN
  rw [derivedCharactersVanishingOn_radical, finrank_top,
    BinaryCarrierDerivedRadical16T1083.relative_character_rank]
  decide

theorem normal_le_radical_of_intersection_le_radical (N : Subgroup Original) [N.Normal]
    (hN : N ⊓ commutator Original ≤ primeRelativeRadical 2 (commutator Original)) :
    N ≤ primeRelativeRadical 2 (commutator Original) := by
  have hd := normal_le_derived_of_intersection_le_radical N hN
  rwa [inf_eq_left.mpr hd] at hN

end BinaryCarrierProperIntersection16T1083

namespace BinaryCarrierProperIntersection16T1084

abbrev Original := BinaryCarrierDerivedOrder16T1084.Original
private abbrev kernelIdentity := BinaryCarrierDerived16T1084.evaluationKernel_eq_commutator

theorem image_finrank_le_two (N : Subgroup Original) [N.Normal]
    (hN : ¬commutator Original ≤ N) :
    Module.finrank (ZMod 2) (primeDerivedImage 2 N) ≤ 2 :=
  primeDerivedImage_finrank_le_of_proper_intersection 2 kernelIdentity
    BinaryCarrierExactOrder16T1084.original_isPGroup 2
    BinaryCarrierFormTransport16T1084.actual_form_finrank_ker_le_two N hN

theorem quotient_log_le_two (N : Subgroup Original) [N.Normal]
    (hN : ¬commutator Original ≤ N) :
    Nat.log 2 (Nat.card (normalChainQuotient (N ⊓ commutator Original) N)) ≤ 2 := by
  rw [derivedIntersectionQuotient_log_card_eq_image 2 kernelIdentity N]
  exact image_finrank_le_two N hN

theorem card_le_4_mul_intersection (N : Subgroup Original) [N.Normal]
    (hN : ¬commutator Original ≤ N) :
    Nat.card N ≤ 4 * Nat.card ↥(N ⊓ commutator Original) :=
  normal_card_le_pow_mul_derivedIntersection 2 kernelIdentity N 2
    (image_finrank_le_two N hN)

theorem normal_le_derived_of_intersection_le_radical (N : Subgroup Original) [N.Normal]
    (hN : N ⊓ commutator Original ≤ primeRelativeRadical 2 (commutator Original)) :
    N ≤ commutator Original := by
  apply derivedCharactersVanishingOn_normal_le_commutator_of_two_le 2 kernelIdentity
    BinaryCarrierFormTransport16T1084.actual_form_ker_inf_eq_bot_of_independent
    (primeRelativeRadical 2 (commutator Original)) N hN
  rw [derivedCharactersVanishingOn_radical, finrank_top,
    BinaryCarrierDerivedRadical16T1084.relative_character_rank]
  decide

theorem normal_le_radical_of_intersection_le_radical (N : Subgroup Original) [N.Normal]
    (hN : N ⊓ commutator Original ≤ primeRelativeRadical 2 (commutator Original)) :
    N ≤ primeRelativeRadical 2 (commutator Original) := by
  have hd := normal_le_derived_of_intersection_le_radical N hN
  rwa [inf_eq_left.mpr hd] at hN

end BinaryCarrierProperIntersection16T1084

namespace BinaryCarrierProperIntersection16T1547

abbrev Original := BinaryCarrierDerivedOrder16T1547.Original
private abbrev kernelIdentity := BinaryCarrierDerived16T1547.evaluationKernel_eq_commutator

theorem image_finrank_le_two (N : Subgroup Original) [N.Normal]
    (hN : ¬commutator Original ≤ N) :
    Module.finrank (ZMod 2) (primeDerivedImage 2 N) ≤ 2 :=
  primeDerivedImage_finrank_le_of_proper_intersection 2 kernelIdentity
    BinaryCarrierExactOrder16T1547.original_isPGroup 2
    BinaryCarrierFormTransport16T1547.actual_form_finrank_ker_le_two N hN

theorem quotient_log_le_two (N : Subgroup Original) [N.Normal]
    (hN : ¬commutator Original ≤ N) :
    Nat.log 2 (Nat.card (normalChainQuotient (N ⊓ commutator Original) N)) ≤ 2 := by
  rw [derivedIntersectionQuotient_log_card_eq_image 2 kernelIdentity N]
  exact image_finrank_le_two N hN

theorem card_le_4_mul_intersection (N : Subgroup Original) [N.Normal]
    (hN : ¬commutator Original ≤ N) :
    Nat.card N ≤ 4 * Nat.card ↥(N ⊓ commutator Original) :=
  normal_card_le_pow_mul_derivedIntersection 2 kernelIdentity N 2
    (image_finrank_le_two N hN)

theorem normal_le_derived_of_intersection_le_radical (N : Subgroup Original) [N.Normal]
    (hN : N ⊓ commutator Original ≤ primeRelativeRadical 2 (commutator Original)) :
    N ≤ commutator Original := by
  apply derivedCharactersVanishingOn_normal_le_commutator_of_two_le 2 kernelIdentity
    BinaryCarrierFormTransport16T1547.actual_form_ker_inf_eq_bot_of_independent
    (primeRelativeRadical 2 (commutator Original)) N hN
  rw [derivedCharactersVanishingOn_radical, finrank_top,
    BinaryCarrierDerivedRadical16T1547.relative_character_rank]
  decide

theorem normal_le_radical_of_intersection_le_radical (N : Subgroup Original) [N.Normal]
    (hN : N ⊓ commutator Original ≤ primeRelativeRadical 2 (commutator Original)) :
    N ≤ primeRelativeRadical 2 (commutator Original) := by
  have hd := normal_le_derived_of_intersection_le_radical N hN
  rwa [inf_eq_left.mpr hd] at hN

end BinaryCarrierProperIntersection16T1547

namespace BinaryCarrierProperIntersection16T1332

abbrev Original := BinaryCarrierDerivedOrder16T1332.Original
private abbrev kernelIdentity := BinaryCarrierDerived16T1332.evaluationKernel_eq_commutator

theorem image_finrank_le_three (N : Subgroup Original) [N.Normal]
    (hN : ¬commutator Original ≤ N) :
    Module.finrank (ZMod 2) (primeDerivedImage 2 N) ≤ 3 := by
  have h := primeDerivedImage_finrank_add_one_le_of_proper_intersection_star 2 kernelIdentity
    BinaryCarrierExactOrder16T1332.original_isPGroup
    BinaryCarrierStarTransport16T1332.characterEquiv
    BinaryCarrierStarTransport16T1332.evaluationEquiv
    BinaryCarrierStarTransport16T1332.actual_form_eq_star N hN
  have hd : Module.finrank (ZMod 2) BinaryCarrierStarTransport16T1332.U = 4 := by simp
  rw [hd] at h
  have hs : Module.finrank (ZMod 2) (primeDerivedImage 2 N) + 1 ≤ 4 := h
  omega

theorem quotient_log_le_three (N : Subgroup Original) [N.Normal]
    (hN : ¬commutator Original ≤ N) :
    Nat.log 2 (Nat.card (normalChainQuotient (N ⊓ commutator Original) N)) ≤ 3 := by
  rw [derivedIntersectionQuotient_log_card_eq_image 2 kernelIdentity N]
  exact image_finrank_le_three N hN

theorem card_le_8_mul_intersection (N : Subgroup Original) [N.Normal]
    (hN : ¬commutator Original ≤ N) :
    Nat.card N ≤ 8 * Nat.card ↥(N ⊓ commutator Original) :=
  normal_card_le_pow_mul_derivedIntersection 2 kernelIdentity N 3
    (image_finrank_le_three N hN)

theorem normal_le_derived_of_intersection_le_radical (N : Subgroup Original) [N.Normal]
    (hN : N ⊓ commutator Original ≤ primeRelativeRadical 2 (commutator Original)) :
    N ≤ commutator Original := by
  have hr : Module.finrank (ZMod 2)
      (derivedCharactersVanishingOn 2 (primeRelativeRadical 2 (commutator Original))) = 4 := by
    rw [derivedCharactersVanishingOn_radical, finrank_top,
      BinaryCarrierDerivedRadical16T1332.relative_character_rank]
  have hp : derivedCharactersVanishingOn 2
      (primeRelativeRadical 2 (commutator Original)) ≠ ⊥ :=
    Submodule.one_le_finrank_iff.mp (by rw [hr]; decide)
  have h := primeDerivedImage_finrank_add_vanishing_le_of_star 2 kernelIdentity
    BinaryCarrierStarTransport16T1332.characterEquiv
    BinaryCarrierStarTransport16T1332.evaluationEquiv
    BinaryCarrierStarTransport16T1332.actual_form_eq_star
    (primeRelativeRadical 2 (commutator Original)) N hN hp
  have hd : Module.finrank (ZMod 2) BinaryCarrierStarTransport16T1332.U = 4 := by simp
  rw [hr, hd] at h
  apply (primeDerivedImage_eq_bot_iff_le_commutator 2 kernelIdentity N).mp
  apply Submodule.finrank_eq_zero.mp
  omega

theorem normal_le_radical_of_intersection_le_radical (N : Subgroup Original) [N.Normal]
    (hN : N ⊓ commutator Original ≤ primeRelativeRadical 2 (commutator Original)) :
    N ≤ primeRelativeRadical 2 (commutator Original) := by
  have hd := normal_le_derived_of_intersection_le_radical N hN
  rwa [inf_eq_left.mpr hd] at hN

end BinaryCarrierProperIntersection16T1332

end SymmetricSubgroupAsymptotics
