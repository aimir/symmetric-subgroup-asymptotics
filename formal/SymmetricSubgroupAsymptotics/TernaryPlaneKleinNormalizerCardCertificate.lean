import SymmetricSubgroupAsymptotics.TernaryPlaneKleinPair

/-!
# Finite cardinal certificate for ternary Klein normalizers

This module contains only the finite calculation showing that the
normalizer of a displayed independent commuting involution pair in
`GL₂(3)` has order eight.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace LinearThree

attribute [-instance] Classical.propDecidable

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def kleinInv0 : GL3 := ofGL !![0, 1; 1, 0] (by decide)
def kleinInv1 : GL3 := ofGL !![0, 2; 2, 0] (by decide)
def kleinInv2 : GL3 := ofGL !![1, 0; 0, 2] (by decide)
def kleinInv3 : GL3 := ofGL !![1, 0; 1, 2] (by decide)
def kleinInv4 : GL3 := ofGL !![1, 0; 2, 2] (by decide)
def kleinInv5 : GL3 := ofGL !![1, 1; 0, 2] (by decide)
def kleinInv6 : GL3 := ofGL !![1, 2; 0, 2] (by decide)
def kleinInv7 : GL3 := ofGL !![2, 0; 0, 1] (by decide)
def kleinInv8 : GL3 := ofGL !![2, 0; 0, 2] (by decide)
def kleinInv9 : GL3 := ofGL !![2, 0; 1, 1] (by decide)
def kleinInv10 : GL3 := ofGL !![2, 0; 2, 1] (by decide)
def kleinInv11 : GL3 := ofGL !![2, 1; 0, 1] (by decide)
def kleinInv12 : GL3 := ofGL !![2, 2; 0, 1] (by decide)

def kleinInvFamily : Fin 13 → GL3 :=
  ![kleinInv0, kleinInv1, kleinInv2, kleinInv3, kleinInv4, kleinInv5,
    kleinInv6, kleinInv7, kleinInv8, kleinInv9, kleinInv10, kleinInv11,
    kleinInv12]

/-- Every nonidentity involution in `GL₂(3)` is one of the thirteen
displayed matrices.  This check ranges over the 81 raw matrices rather than
over units carrying proof fields. -/
theorem matrix_involution_mem_kleinInvFamily :
    ∀ A : M2, A ∈ glSet → A ≠ 1 → A * A = 1 →
      ∃ i : Fin 13, A = (kleinInvFamily i : M2) := by
  decide +kernel

/-- The admissible indexed pairs generate one of six literal Klein four
subgroups. -/
theorem kleinInvFamily_representative :
    ∀ i j : Fin 13,
      ¬ (kleinInvFamily i ≠ 1 ∧ kleinInvFamily j ≠ 1 ∧
        kleinInvFamily i ≠ kleinInvFamily j ∧
        (kleinInvFamily i) ^ 2 = 1 ∧ (kleinInvFamily j) ^ 2 = 1 ∧
        kleinInvFamily i * kleinInvFamily j =
          kleinInvFamily j * kleinInvFamily i) ∨
      kleinFourElements (kleinInvFamily i) (kleinInvFamily j) =
          kleinFourElements kleinInv0 kleinInv1 ∨
      kleinFourElements (kleinInvFamily i) (kleinInvFamily j) =
          kleinFourElements kleinInv2 kleinInv7 ∨
      kleinFourElements (kleinInvFamily i) (kleinInvFamily j) =
          kleinFourElements kleinInv3 kleinInv10 ∨
      kleinFourElements (kleinInvFamily i) (kleinInvFamily j) =
          kleinFourElements kleinInv4 kleinInv9 ∨
      kleinFourElements (kleinInvFamily i) (kleinInvFamily j) =
          kleinFourElements kleinInv5 kleinInv12 ∨
      kleinFourElements (kleinInvFamily i) (kleinInvFamily j) =
          kleinFourElements kleinInv6 kleinInv11 := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem kleinPairRepresentative0_certificate :
    (kleinNormalizerFinset kleinInv0 kleinInv1).card = 8 := by
  decide +kernel

private theorem kleinPairRepresentative1_certificate :
    (kleinNormalizerFinset kleinInv2 kleinInv7).card = 8 := by
  decide +kernel

private theorem kleinPairRepresentative2_certificate :
    (kleinNormalizerFinset kleinInv3 kleinInv10).card = 8 := by
  decide +kernel

private theorem kleinPairRepresentative3_certificate :
    (kleinNormalizerFinset kleinInv4 kleinInv9).card = 8 := by
  decide +kernel

private theorem kleinPairRepresentative4_certificate :
    (kleinNormalizerFinset kleinInv5 kleinInv12).card = 8 := by
  decide +kernel

private theorem kleinPairRepresentative5_certificate :
    (kleinNormalizerFinset kleinInv6 kleinInv11).card = 8 := by
  decide +kernel

/-- The computable normalizer filter has eight elements for every
independent commuting involution pair.  Unlike `Nat.card` of a subgroup,
this statement reduces only the explicit `Finset` enumerator. -/
theorem kleinNormalizerFinset_card_eq_eight_certificate :
    ∀ a b : GL3,
      a ≠ 1 → b ≠ 1 → a ≠ b →
      a ^ 2 = 1 → b ^ 2 = 1 → a * b = b * a →
      (kleinNormalizerFinset a b).card = 8 := by
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
  · simpa only [kleinNormalizerFinset, conjugatedKleinFourElements, h] using
      kleinPairRepresentative0_certificate
  · simpa only [kleinNormalizerFinset, conjugatedKleinFourElements, h] using
      kleinPairRepresentative1_certificate
  · simpa only [kleinNormalizerFinset, conjugatedKleinFourElements, h] using
      kleinPairRepresentative2_certificate
  · simpa only [kleinNormalizerFinset, conjugatedKleinFourElements, h] using
      kleinPairRepresentative3_certificate
  · simpa only [kleinNormalizerFinset, conjugatedKleinFourElements, h] using
      kleinPairRepresentative4_certificate
  · simpa only [kleinNormalizerFinset, conjugatedKleinFourElements, h] using
      kleinPairRepresentative5_certificate

/-- Bridge the computable filter cardinal to the actual subgroup
normalizer. -/
theorem pair_normalizer_card_eq_eight_certificate
    (a b : GL3)
    (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b)
    (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1)
    (hcomm : a * b = b * a) :
    Nat.card (Subgroup.normalizer (kleinPairSubgroup a b : Set GL3)) = 8 := by
  set_option maxRecDepth 100000 in
    let e :
        Subgroup.normalizer (kleinPairSubgroup a b : Set GL3) ≃
          {g : GL3 // g ∈ kleinNormalizerFinset a b} :=
      { toFun := fun g =>
          ⟨g.1, (mem_kleinNormalizerFinset_iff a b g.1 ha2 hb2 hcomm).mpr g.2⟩
        invFun := fun g =>
          ⟨g.1, (mem_kleinNormalizerFinset_iff a b g.1 ha2 hb2 hcomm).mp g.2⟩
        left_inv := fun g => Subtype.ext rfl
        right_inv := fun g => Subtype.ext rfl }
    calc
      Nat.card (Subgroup.normalizer (kleinPairSubgroup a b : Set GL3)) =
          Nat.card {g : GL3 // g ∈ kleinNormalizerFinset a b} :=
        Nat.card_congr e
      _ = (kleinNormalizerFinset a b).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      _ = 8 := kleinNormalizerFinset_card_eq_eight_certificate
        a b ha hb hab ha2 hb2 hcomm

end LinearThree
end SymmetricSubgroupAsymptotics

end
