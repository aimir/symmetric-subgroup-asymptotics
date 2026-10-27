import SymmetricSubgroupAsymptotics.MathieuTwentyThreeTwentyFourParityOuterReduction
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourActualIndexSquare
import SymmetricSubgroupAsymptotics.FixedProductAutomorphismIncidence

/-! One normalized swap fibre in the original faithful M24 action.
No abstract automorphism acts on the point set: only its actual image
of the source generator is evaluated by the original representation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourSwapFibreOuterReduction
open PrimitiveSocleRawStructure OuterFixedElementEvaluationBound
open CFSG.Models.Presentations.M24
open CFSGMathieuTwentyFourActualRepresentation CFSGMathieuTwentyFourGoodSylowTwentyThree
open MathieuPrimeCycleOddNormalizerWitnesses

def product : Model := pinnedX*pinnedY
def base : Fin 24 := 8

theorem product_image_eq : permutationRepresentation product = m24Cycle := by
  rw [product,map_mul]
  exact congrArg₂ (fun u v : Equiv.Perm (Fin 24) => u*v)
    permutationRepresentation_of_zero permutationRepresentation_of_one

private theorem table_unique_fixed :
    ∀ i : Fin 24, m24Cycle i=i ↔ i=(8 : Fin 24) := by decide +kernel

theorem product_unique_fixed (i : Fin 24) :
    permutationRepresentation product i=i ↔ i=base := by
  rw [product_image_eq]
  exact table_unique_fixed i

theorem product_fixes_base : permutationRepresentation product base=base :=
  (product_unique_fixed base).mpr rfl

theorem x_image_base : permutationRepresentation pinnedX base=(11 : Fin 24) := by
  change permutationRepresentation (PresentedGroup.of (0 : Fin 2)) base=11
  rw [permutationRepresentation_of_zero]
  decide +kernel

theorem x_moves_base : permutationRepresentation pinnedX base ≠ base := by
  rw [x_image_base]
  decide +kernel

theorem product_transitive_off_base :
    ∀ p q : {i : Fin 24 // i ≠ base}, ∃ k : ℤ,
      permutationRepresentation (product^k) p.val=q.val := by
  have htype : (permutationRepresentation product).cycleType={23} := pinnedProduct_cycleType
  have hc : (permutationRepresentation product).IsCycle :=
    Equiv.Perm.card_cycleType_eq_one.mp (by rw [htype]; rfl)
  intro p q
  have hp : permutationRepresentation product p.val ≠ p.val := by
    intro h
    exact p.property ((product_unique_fixed p.val).mp h)
  have hq : permutationRepresentation product q.val ≠ q.val := by
    intro h
    exact q.property ((product_unique_fixed q.val).mp h)
  obtain ⟨k,hk⟩ := hc.sameCycle hp hq
  refine ⟨k,?_⟩
  rw [map_zpow]
  exact hk

theorem original_product_pair_closure :
    Subgroup.closure ({pinnedX,product} : Set Model)=⊤ :=
  SimpleInvolutionPrimeCycleGoodSylow.closure_involution_product
    pinnedX pinnedY presentation_pair_closure

theorem fixed_images_move_base (f : fixedAutomorphisms product) :
    permutationRepresentation (f.val pinnedX) base ≠ base :=
  FixedProductAutomorphismIncidence.image_moves_of_generates
    permutationRepresentation pinnedX product base original_product_pair_closure
    product_fixes_base x_moves_base f

/-- Literal normalized fibre: fixes the product, and its x-image sends
the unique product-fixed point to the original x-image of that point. -/
def SwapFibre := {f : fixedAutomorphisms product //
  permutationRepresentation (f.val pinnedX) base=permutationRepresentation pinnedX base}

theorem swap_fibre_reverse (f : SwapFibre) :
    permutationRepresentation (f.val.val pinnedX)
      (permutationRepresentation pinnedX base)=base := by
  have hh := FixedProductAutomorphismIncidence.image_swap_of_involution
    permutationRepresentation pinnedX product pinnedX_square f.val base
  rw [f.property] at hh
  exact hh

theorem moved_points_card : Nat.card {i : Fin 24 // i ≠ base}=23 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem fixed_card_eq_twentyThree_mul_swap [Finite Model] :
    Nat.card (fixedAutomorphisms product)=23*Nat.card SwapFibre := by
  have hh := FixedProductAutomorphismIncidence.fixed_card_eq_moved_fibre
    permutationRepresentation pinnedX product base product_fixes_base fixed_images_move_base
    product_transitive_off_base
    (⟨permutationRepresentation pinnedX base,x_moves_base⟩ : {i : Fin 24 // i ≠ base})
  rw [moved_points_card] at hh
  exact hh

theorem outer_card_le_twice_swap [Finite Model] [IsSimpleGroup Model] :
    Nat.card (Outer Model) ≤ 2*Nat.card SwapFibre := by
  apply FixedProductAutomorphismIncidence.outer_moved_fibre_bound
    permutationRepresentation pinnedX product base product_fixes_base fixed_images_move_base
    product_transitive_off_base
    (⟨permutationRepresentation pinnedX base,x_moves_base⟩ : {i : Fin 24 // i ≠ base})
  rw [moved_points_card]
  exact CFSGMathieuTwentyFourParityOuterReduction.prime_mul_outer_le_twice_fixed
    CFSGMathieuTwentyFourActualIndexSquare.model_noncommutative

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourSwapFibreOuterReduction
