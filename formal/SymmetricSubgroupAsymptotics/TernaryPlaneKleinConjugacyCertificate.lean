import SymmetricSubgroupAsymptotics.TernaryPlaneKleinNormalizerCardCertificate

/-!
# Finite conjugacy certificate for ternary Klein pairs

This module contains only the finite search carrying a displayed
independent commuting involution pair in `GL₂(3)` to the standard diagonal
Klein four.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace LinearThree

attribute [-instance] Classical.propDecidable
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private def kleinConj0 : GL3 := ofGL !![1, 1; 1, 2] (by decide)
private def kleinConj1 : GL3 := 1
private def kleinConj2 : GL3 := ofGL !![1, 0; 1, 1] (by decide)
private def kleinConj3 : GL3 := ofGL !![1, 0; 1, 2] (by decide)
private def kleinConj4 : GL3 := ofGL !![0, 1; 1, 2] (by decide)
private def kleinConj5 : GL3 := ofGL !![0, 1; 1, 1] (by decide)

private theorem standardKleinFourElements_eq_representative :
    kleinFourElements
        (DegreeSixS3Wreath.standardKleinLinearMap kleinFirstBit)
        (DegreeSixS3Wreath.standardKleinLinearMap kleinSecondBit) =
      kleinFourElements kleinInv2 kleinInv7 := by
  decide +kernel

private theorem kleinRepresentative0_conjugate :
    conjugatedKleinFourElements kleinInv0 kleinInv1 kleinConj0 =
      kleinFourElements kleinInv2 kleinInv7 := by decide +kernel

private theorem kleinRepresentative1_conjugate :
    conjugatedKleinFourElements kleinInv2 kleinInv7 kleinConj1 =
      kleinFourElements kleinInv2 kleinInv7 := by decide +kernel

private theorem kleinRepresentative2_conjugate :
    conjugatedKleinFourElements kleinInv3 kleinInv10 kleinConj2 =
      kleinFourElements kleinInv2 kleinInv7 := by decide +kernel

private theorem kleinRepresentative3_conjugate :
    conjugatedKleinFourElements kleinInv4 kleinInv9 kleinConj3 =
      kleinFourElements kleinInv2 kleinInv7 := by decide +kernel

private theorem kleinRepresentative4_conjugate :
    conjugatedKleinFourElements kleinInv5 kleinInv12 kleinConj4 =
      kleinFourElements kleinInv2 kleinInv7 := by decide +kernel

private theorem kleinRepresentative5_conjugate :
    conjugatedKleinFourElements kleinInv6 kleinInv11 kleinConj5 =
      kleinFourElements kleinInv2 kleinInv7 := by decide +kernel

/-- The finite search is stated entirely as equality of four-element
`Finset`s, so its decision procedure never unfolds subgroup closure or a
classical finite instance. -/
theorem pair_conjugate_standardKleinFinset_certificate :
    ∀ a b : GL3,
      a ≠ 1 → b ≠ 1 → a ≠ b →
      a ^ 2 = 1 → b ^ 2 = 1 → a * b = b * a →
      ∃ g : GL3,
        conjugatedKleinFourElements a b g =
          kleinFourElements
            (DegreeSixS3Wreath.standardKleinLinearMap kleinFirstBit)
            (DegreeSixS3Wreath.standardKleinLinearMap kleinSecondBit) := by
  intro a b ha hb hab ha2 hb2 hcomm
  have haM : (a : M2) ≠ 1 := fun h => ha (Units.ext h)
  have hbM : (b : M2) ≠ 1 := fun h => hb (Units.ext h)
  have ha2M : (a : M2) * (a : M2) = 1 := by
    simpa only [pow_two, Units.val_mul, Units.val_one] using congrArg Units.val ha2
  have hb2M : (b : M2) * (b : M2) = 1 := by
    simpa only [pow_two, Units.val_mul, Units.val_one] using congrArg Units.val hb2
  obtain ⟨i, hi⟩ := matrix_involution_mem_kleinInvFamily
    (a : M2) (coe_mem_glSet a) haM ha2M
  obtain ⟨j, hj⟩ := matrix_involution_mem_kleinInvFamily
    (b : M2) (coe_mem_glSet b) hbM hb2M
  have hai : a = kleinInvFamily i := Units.ext hi
  have hbj : b = kleinInvFamily j := Units.ext hj
  subst a
  subst b
  have hclass := kleinInvFamily_representative i j
  rcases hclass with hbad | h | h | h | h | h | h
  · exact (hbad ⟨ha, hb, hab, ha2, hb2, hcomm⟩).elim
  · refine ⟨kleinConj0, ?_⟩
    simpa only [conjugatedKleinFourElements, h,
      standardKleinFourElements_eq_representative] using
        kleinRepresentative0_conjugate
  · refine ⟨kleinConj1, ?_⟩
    simpa only [conjugatedKleinFourElements, h,
      standardKleinFourElements_eq_representative] using
        kleinRepresentative1_conjugate
  · refine ⟨kleinConj2, ?_⟩
    simpa only [conjugatedKleinFourElements, h,
      standardKleinFourElements_eq_representative] using
        kleinRepresentative2_conjugate
  · refine ⟨kleinConj3, ?_⟩
    simpa only [conjugatedKleinFourElements, h,
      standardKleinFourElements_eq_representative] using
        kleinRepresentative3_conjugate
  · refine ⟨kleinConj4, ?_⟩
    simpa only [conjugatedKleinFourElements, h,
      standardKleinFourElements_eq_representative] using
        kleinRepresentative4_conjugate
  · refine ⟨kleinConj5, ?_⟩
    simpa only [conjugatedKleinFourElements, h,
      standardKleinFourElements_eq_representative] using
        kleinRepresentative5_conjugate

/-- Structural bridge from the finite four-element certificate to the
actual generated subgroups. -/
theorem pair_conjugate_standardKlein_certificate
    (a b : GL3)
    (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b)
    (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1)
    (hcomm : a * b = b * a) :
    ∃ g : GL3,
      (kleinPairSubgroup a b).map (MulAut.conj g).toMonoidHom =
        DegreeSixS3Wreath.standardKleinLinearMap.range := by
  obtain ⟨g, hg⟩ := pair_conjugate_standardKleinFinset_certificate
    a b ha hb hab ha2 hb2 hcomm
  refine ⟨g, ?_⟩
  let f := DegreeSixS3Wreath.standardKleinLinearMap
  have hf2a : (f kleinFirstBit) ^ 2 = 1 :=
    map_kleinFirstBit_square f
  have hf2b : (f kleinSecondBit) ^ 2 = 1 :=
    map_kleinSecondBit_square f
  have hfcomm : f kleinFirstBit * f kleinSecondBit =
      f kleinSecondBit * f kleinFirstBit :=
    map_kleinBits_commute f
  rw [kleinPairSubgroup_eq_kleinFourSubgroup a b ha2 hb2 hcomm,
    binaryKleinRange_eq_pairSubgroup f
      DegreeSixS3Wreath.standardKleinLinearMap_injective,
    kleinPairSubgroup_eq_kleinFourSubgroup
      (f kleinFirstBit) (f kleinSecondBit) hf2a hf2b hfcomm]
  exact map_kleinFourSubgroup_eq_of_conjugated_elements_eq
    a b (f kleinFirstBit) (f kleinSecondBit) g
    ha2 hb2 hcomm hf2a hf2b hfcomm hg

end LinearThree
end SymmetricSubgroupAsymptotics

end
