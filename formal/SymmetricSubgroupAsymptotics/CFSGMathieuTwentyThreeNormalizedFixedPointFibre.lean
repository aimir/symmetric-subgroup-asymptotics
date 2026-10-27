import SymmetricSubgroupAsymptotics.EvenInvolutionFixedPointLowerBound
import SymmetricSubgroupAsymptotics.FixedProductAutomorphismIncidence
import SymmetricSubgroupAsymptotics.MathieuTwentyThreeTwentyFourParityOuterReduction

/-! The SAME pinned M23 fixed-product automorphisms are normalized by
actual inner powers of the product23-cycle. The normalized point fibre
remains explicit; no finite capacity or automorphism-extension premise
is assumed. The original representation is the checked faithful action. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeNormalizedFixedPointFibre
open CFSG.Models.Presentations.M23 PrimitiveSocleRawStructure
open CFSGMathieuTwentyThreeActualRepresentation
open CFSGMathieuTwentyThreeGoodSylowTwentyThree
open OuterFixedElementEvaluationBound

def product : Model := pinnedX * pinnedY

def pointFibre (p : Fin 23) : Type :=
  {f : fixedAutomorphisms product // permutationRepresentation (f.val pinnedX) p = p}

theorem product_zpow_transitive (p q : Fin 23) :
    ∃ k : ℤ, permutationRepresentation (product ^ k) p = q := by
  let sigma := permutationRepresentation product
  have htype : sigma.cycleType = {23} := pinnedProduct_cycleType
  have hcycle : sigma.IsCycle := Equiv.Perm.card_cycleType_eq_one.mp (by
    rw [htype,Multiset.card_singleton])
  have hsupport : sigma.support = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [←sigma.sum_cycleType,htype,Multiset.sum_singleton,Fintype.card_fin]
  have hmove (r : Fin 23) : sigma r ≠ r := by
    apply Equiv.Perm.mem_support.mp
    rw [hsupport]
    exact Finset.mem_univ r
  obtain ⟨k,hk⟩ := hcycle.exists_zpow_eq (hmove p) (hmove q)
  refine ⟨k,?_⟩
  simpa only [map_zpow] using hk

theorem image_fixed_card_ge_three [Finite Model] [IsSimpleGroup Model]
    (hnon : ¬IsMulCommutative Model) (f : fixedAutomorphisms product) :
    3 ≤ Nat.card {p : Fin 23 // permutationRepresentation (f.val pinnedX) p = p} := by
  letI : MulAction Model (Fin 23) := MulAction.compHom (Fin 23) permutationRepresentation
  letI : FaithfulSMul Model (Fin 23) := {
    eq_of_smul_eq_smul := fun {g h} he =>
      permutationRepresentation_injective (Equiv.Perm.ext he) }
  have hsquare : permutationRepresentation (f.val pinnedX) ^ 2 = 1 := by
    rw [←map_pow,←map_pow,pinnedX_square,map_one,map_one]
  have hsign := PrimeCycleParityNormalizer.source_sign_one (G := Model) (n := 23)
    hnon (f.val pinnedX)
  have he : MulAction.toPermHom Model (Fin 23) (f.val pinnedX) =
      permutationRepresentation (f.val pinnedX) := by
    ext p
    rfl
  rw [he] at hsign
  exact EvenInvolutionFixedPointLowerBound.three_le_fixed_card_fin_twentyThree
    _ hsquare hsign

theorem fixed_card_incidence_bound [Finite Model] [IsSimpleGroup Model]
    (hnon : ¬IsMulCommutative Model) :
    3 * Nat.card (fixedAutomorphisms product) ≤ 23 * Nat.card (pointFibre 0) := by
  simpa only [Nat.card_fin,pointFibre] using
    FixedProductAutomorphismIncidence.fixed_point_incidence_lower
      permutationRepresentation pinnedX product (0 : Fin 23) 3
      product_zpow_transitive (image_fixed_card_ge_three hnon)

theorem three_mul_outer_card_le_twice_pointFibre [Finite Model] [IsSimpleGroup Model]
    (hnon : ¬IsMulCommutative Model) :
    3 * Nat.card (Outer Model) ≤ 2 * Nat.card (pointFibre 0) := by
  have houter : Nat.card (Fin 23) * Nat.card (Outer Model) ≤
      2 * Nat.card (fixedAutomorphisms product) := by
    simpa only [Nat.card_fin,product] using
      CFSGMathieuTwentyThreeParityOuterReduction.prime_mul_outer_le_twice_fixed hnon
  exact FixedProductAutomorphismIncidence.outer_fixed_point_fibre_bound
    permutationRepresentation pinnedX product (0 : Fin 23) 3
    product_zpow_transitive (image_fixed_card_ge_three hnon) houter

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreeNormalizedFixedPointFibre
