import SymmetricSubgroupAsymptotics.CFSGFFourOppositeCartanActions
import SymmetricSubgroupAsymptotics.CFSGFFourE6PositiveCartanKernel
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalGoodSylow
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOppositeIntersection

/-! The actual positive and negative folded F4 groups have DISJOINT
images in the SAME original action image. Equality of actions is tested
on the actual four tensor-lattice Cartans, then opposite triangular
supports and the proved positive Cartan centralizer force triviality.
No central-kernel assertion for the full folded group is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6OppositeActionImages
open CFSGFFourSerreMatrices CFSGFFourOriginalGoodSylow CFSGFFourE6CartanDiagonals
open CFSGFFourGradedCartanAction CFSGFFourE6PositiveCartanKernel CFSGFFourOppositeCartanActions
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoCoordinateHeight CFSGNormTwoGeckHeightSupport CFSGNormTwoGeckOppositeIntersection
open CFSGGradedMatrixSubgroups CFSGTwistedE6GeckPositiveTwist CFSGSerreQuadraticMatrix

local instance actionRootDecEq : DecidableEq
    (CFSGNormTwoRootPairing.Roots CartanMatrix.E₆) := Classical.decEq _

private def ambientHeight : Index → ℤ :=
  weight CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base coordinateHeight

def cartanTensor (K : Type) [Field K] (i : Fin 4) : (baseChange realizationData K).range :=
  (baseChange realizationData K).rangeRestrict
    (1 ⊗ₜ[ℤ] CFSGSerreDiagram.latticeGenerator CartanMatrix.F₄ (.H i))

theorem cartanTensor_val (K : Type) [Field K] (i : Fin 4) :
    (cartanTensor K i).val=fieldCartan K i := by
  change baseChange realizationData K
    (1 ⊗ₜ[ℤ] CFSGSerreDiagram.latticeGenerator CartanMatrix.F₄ (.H i)) = _
  rw [baseChange_generator]
  rfl

theorem natural_action_cartan (K : Type) [Field K]
    (g : canonicalElementaryGroup realizationData K) (i : Fin 4) :
    (fullNaturalImageAction K g (cartanTensor K i)).val =
      (g.val : Matrix Index Index K) * fieldCartan K i *
        (↑(g.val⁻¹) : Matrix Index Index K) := by
  change (g.val : Matrix Index Index K) * (cartanTensor K i).val *
    (↑(g.val⁻¹) : Matrix Index Index K) = _
  rw [cartanTensor_val]

theorem positive_eq_one_of_opposite_action_eq (K : Type) [Field K]
    (g h : canonicalElementaryGroup realizationData K)
    (hg : g.val∈Positive K) (hh : h.val∈Negative K)
    (he : fullNaturalImageAction K g=fullNaturalImageAction K h) : g=1 := by
  have hp : g.val∈strictUnits ambientHeight :=
    positive_le_strict CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
      E6Base E6Index coordinateHeight (simple_height CartanMatrix.E₆ CartanMatrix.E₆_diag
        CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos) K hg
  have hn : h.val∈strictUnits (fun a=> -ambientHeight a) :=
    negative_le_strict_opposite CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
      E6Base E6Index coordinateHeight (simple_height CartanMatrix.E₆ CartanMatrix.E₆_diag
        CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos) K hh
  have hc (i : Fin 4) : Commute (g.val : Matrix Index Index K) (fieldCartan K i) := by
    have hv := congrArg Subtype.val (DFunLike.congr_fun he (cartanTensor K i))
    change (fullNaturalImageAction K g (cartanTensor K i)).val =
      (fullNaturalImageAction K h (cartanTensor K i)).val at hv
    rw [natural_action_cartan,natural_action_cartan] at hv
    have hd : (g.val : Matrix Index Index K) * fieldCartan K i *
        (↑(g.val⁻¹) : Matrix Index Index K) = fieldCartan K i := by
      simp only [fieldCartan_eq_diagonal] at hv ⊢
      exact opposite_equal_cartan_action_fixes ambientHeight g.val h.val hp hn
        (fun a : Index=>(cartanFunctional i (rootWeight a) : K)) hv
    have hm := congrArg (fun M : Matrix Index Index K=>M * (g.val : Matrix Index Index K)) hd
    simpa only [mul_assoc,Units.inv_mul,mul_one] using hm
  let u : Positive K := ⟨g.val,hg⟩
  have hu : u=1 := positive_cartan_centralizer_trivial K u hc
  apply Subtype.ext
  have hv := congrArg (fun z : Positive K=>z.val) hu
  change g.val=1 at hv
  exact hv

def positivePart (K : Type) [Field K] : Subgroup (canonicalElementaryGroup realizationData K) :=
  (Positive K).subgroupOf (canonicalElementaryGroup realizationData K)

def negativePart (K : Type) [Field K] : Subgroup (canonicalElementaryGroup realizationData K) :=
  (Negative K).subgroupOf (canonicalElementaryGroup realizationData K)

theorem opposite_action_images_disjoint (K : Type) [Field K] :
    (positivePart K).map (foldedToImage K) ⊓ (negativePart K).map (foldedToImage K)=⊥ := by
  apply le_antisymm _ bot_le
  rintro x ⟨⟨g,hg,rfl⟩,h,hh,he⟩
  have hraw := congrArg (fun z : imageGroup K=>z.val) he.symm
  change fullNaturalImageAction K g=fullNaturalImageAction K h at hraw
  have hg1 := positive_eq_one_of_opposite_action_eq K g h hg hh hraw
  simpa only [hg1,map_one,Subgroup.mem_bot]

end SymmetricSubgroupAsymptotics.CFSGFFourE6OppositeActionImages
