import SymmetricSubgroupAsymptotics.CentralBinaryRecursiveCompleteQuotientComparison
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockQStarBinaryQuotients

/-!
# Uniform recursive comparison for groups of order four

Every group of order four is a binary group.  Applying the finite p-group
center theorem to the whole group chooses a central subgroup of order two;
the quotient has order two and hence is canonically isomorphic, up to
choice, to `C₂`.  This gives one recursive central-binary step without
splitting into cyclic and Klein-four cases.

The rank-one through rank-four elementary quotients of `QStar` then control
the group itself, its product with `C₂`, and its product with two copies of
`C₂`.  These are exactly the three inputs needed by the two projective
kernel factors in the four-block two-sign argument.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

private abbrev C2 := Multiplicative (ZMod 2)

namespace OrderFourCentralBinaryRecursiveComparison

variable (A : Type*) [Group A] [Finite A]

/-- A chosen central order-two axis in an arbitrary group of order four. -/
noncomputable def centralSeries (hA : Nat.card A = 4) :
    BinaryNormalKernelCentralSeries A (⊤ : Subgroup A) := by
  haveI : Nontrivial A :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hA]; norm_num)
  have hpower : Nat.card A = 2 ^ 2 := by rw [hA]; norm_num
  exact binaryNormalKernelCentralSeries_of_card_le_four
    (IsPGroup.of_card hpower) (⊤ : Subgroup A) top_ne_bot (by simp [hA])

theorem quotient_card (hA : Nat.card A = 4) :
    Nat.card (A ⧸ (centralSeries A hA).C) = 2 := by
  let S := centralSeries A hA
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup S.C
  rw [hA, S.C_card] at hmul
  omega

/-- The quotient by the chosen central axis, identified with `C₂`. -/
noncomputable def quotientEquiv (hA : Nat.card A = 4) :
    A ⧸ (centralSeries A hA).C ≃* C2 :=
  mulEquivOfPrimeCardEq (quotient_card A hA) (by norm_num [C2, Nat.card_zmod])

/-- The actual central binary projection of an order-four group. -/
noncomputable def projection (hA : Nat.card A = 4) : A →* C2 :=
  (quotientEquiv A hA).toMonoidHom.comp
    (QuotientGroup.mk' (centralSeries A hA).C)

theorem projection_surjective (hA : Nat.card A = 4) :
    Function.Surjective (projection A hA) :=
  (quotientEquiv A hA).surjective.comp
    (QuotientGroup.mk'_surjective (centralSeries A hA).C)

theorem projection_ker (hA : Nat.card A = 4) :
    (projection A hA).ker = (centralSeries A hA).C := by
  let S := centralSeries A hA
  let e := quotientEquiv A hA
  ext x
  change e (QuotientGroup.mk' S.C x) = 1 ↔ x ∈ S.C
  constructor
  · intro hx
    apply QuotientGroup.eq_one_iff.mp
    apply e.injective
    simpa only [map_one] using hx
  · intro hx
    rw [QuotientGroup.eq_one_iff.mpr hx, map_one]

/-- Direct `QStar` data for the central binary quotient of any order-four
group. -/
noncomputable def globalComparison (hA : Nat.card A = 4) :
    CentralBinaryGlobalComparison
      DegreeThreeFourBlockTwoSignComparator.QStarGroup A C2 := by
  let S := centralSeries A hA
  refine
    { projection := projection A hA
      projection_surjective := projection_surjective A hA
      central_kernel := ?_
      kernel_card_le_two := ?_
      baseQuotient :=
        DegreeThreeFourBlockTwoSignComparator.qStarToBinary1
      baseQuotient_surjective :=
        DegreeThreeFourBlockTwoSignComparator.qStarToBinary1_surjective
      productQuotient :=
        DegreeThreeFourBlockTwoSignComparator.qStarToBinary2
      productQuotient_surjective :=
        DegreeThreeFourBlockTwoSignComparator.qStarToBinary2_surjective }
  · intro z hz x
    have hzC : z ∈ S.C := by
      rw [← projection_ker A hA]
      exact hz
    exact Subgroup.mem_center_iff.mp (S.C_le_center hzC) x
  · rw [projection_ker A hA, S.C_card]

/-- Recursive comparison for an arbitrary group of order four. -/
noncomputable def comparison (hA : Nat.card A = 4) :
    CentralBinaryRecursiveComparison
      DegreeThreeFourBlockTwoSignComparator.QStarGroup A C2 :=
  CentralBinaryRecursiveComparison.ofGlobal (globalComparison A hA)

/-- Recursive comparison after adjoining one binary factor. -/
noncomputable def productComparison (hA : Nat.card A = 4) :
    CentralBinaryRecursiveComparison
      DegreeThreeFourBlockTwoSignComparator.QStarGroup
      (A × C2) (C2 × C2) := by
  let D := comparison A hA
  apply D.prodC2 1
  intro b J
  simpa only [Nat.cast_one, one_mul] using
    completeQuotientWeight_le_of_surjective
      DegreeThreeFourBlockTwoSignComparator.qStarToBinary3
      DegreeThreeFourBlockTwoSignComparator.qStarToBinary3_surjective J

/-- Recursive comparison after adjoining two binary factors. -/
noncomputable def doubleProductComparison (hA : Nat.card A = 4) :
    CentralBinaryRecursiveComparison
      DegreeThreeFourBlockTwoSignComparator.QStarGroup
      ((A × C2) × C2) ((C2 × C2) × C2) := by
  let D := productComparison A hA
  apply D.prodC2 1
  intro b J
  simpa only [Nat.cast_one, one_mul] using
    completeQuotientWeight_le_of_surjective
      DegreeThreeFourBlockTwoSignComparator.qStarToBinary4
      DegreeThreeFourBlockTwoSignComparator.qStarToBinary4_surjective J

/-- A small uniform coefficient for the order-four comparison. -/
theorem comparison_coefficient_le (hA : Nat.card A = 4) :
    (comparison A hA).coefficient ≤ 2 ^ 7 := by
  let D := comparison A hA
  apply D.coefficient_le_two_pow 2 2 0
  · rw [hA]
  · norm_num [C2, Nat.card_zmod]
  · change 1 ≤ 2 ^ 0
    norm_num
  · change 1 ≤ 2 ^ 0
    norm_num

/-- A uniform coefficient after adjoining one binary factor. -/
theorem productComparison_coefficient_le (hA : Nat.card A = 4) :
    (productComparison A hA).coefficient ≤ 2 ^ 14 := by
  let D := productComparison A hA
  apply D.coefficient_le_two_pow 3 4 0
  · rw [Nat.card_prod, hA]
    norm_num [C2, Nat.card_zmod]
  · norm_num [C2, Nat.card_zmod]
  · change 1 ≤ 2 ^ 0
    norm_num
  · change 1 ≤ 2 ^ 0
    norm_num

/-- A uniform coefficient after adjoining two binary factors. -/
theorem doubleProductComparison_coefficient_le (hA : Nat.card A = 4) :
    (doubleProductComparison A hA).coefficient ≤ 2 ^ 25 := by
  let D := doubleProductComparison A hA
  apply D.coefficient_le_two_pow 4 8 0
  · rw [Nat.card_prod, Nat.card_prod, hA]
    norm_num [C2, Nat.card_zmod]
  · norm_num [C2, Nat.card_zmod]
  · change 1 ≤ 2 ^ 0
    norm_num
  · change 1 ≤ 2 ^ 0
    norm_num

end OrderFourCentralBinaryRecursiveComparison
end SymmetricSubgroupAsymptotics

end
