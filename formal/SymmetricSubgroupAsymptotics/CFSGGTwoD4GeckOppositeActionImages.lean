import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckPositiveCartanKernel
import SymmetricSubgroupAsymptotics.CFSGFFourOppositeCartanActions
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOppositeIntersection

/-! The two original G2 Cartan tensors separate opposite D4 unipotent
images in the SAME cubic integral-image action. In particular this is
an actual disjointness proof, independent of any full-kernel centrality
or representation-faithfulness assertion. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOppositeActionImages
open CFSGGTwoD4GeckGenerators CFSGGTwoD4GeckIntegralRealization
open CFSGGTwoD4GeckImageRealization CFSGGTwoD4GeckCartanDiagonals
open CFSGGTwoD4GeckPositiveCartanKernel CFSGFFourGradedCartanAction
open CFSGFFourOppositeCartanActions CFSGTrialityD4NormTwo
open CFSGTrialityGeckPositiveTwist CFSGNormTwoCoordinateHeight
open CFSGNormTwoGeckHeightSupport CFSGNormTwoGeckOppositeIntersection
open CFSGGradedMatrixSubgroups CFSGNormTwoGeckPositivePGroup

private def ambientHeight : GeckIndex→ℤ :=
  weight (CartanMatrix.D 4) (CartanMatrix.D_transpose 4) D4_positive_definite Base coordinateHeight

abbrev Negative (K : Type) [Field K] :=
  rootGroup (CartanMatrix.D 4) (CartanMatrix.D_transpose 4) D4_positive_definite Base Index K true

def cartanTensor (K : Type) [Field K] (i : Fin 2) : Image K :=
  (CFSGSerreCubicMatrix.baseChange realizationData K).rangeRestrict
    (1 ⊗ₜ[ℤ] CFSGSerreDiagram.latticeGenerator CartanMatrix.G₂ (.H i))

theorem cartanTensor_val (K : Type) [Field K] (i : Fin 2) :
    (cartanTensor K i).val=fieldCartan K i := by
  change CFSGSerreCubicMatrix.baseChange realizationData K
    (1 ⊗ₜ[ℤ] CFSGSerreDiagram.latticeGenerator CartanMatrix.G₂ (.H i)) = _
  rw [CFSGSerreCubicMatrix.baseChange_generator]
  rfl

theorem folded_action_cartan (K : Type) [Field K] (g : foldedGroup K) (i : Fin 2) :
    (foldedImageAction K g (cartanTensor K i)).val =
      (g.val : Matrix GeckIndex GeckIndex K)*fieldCartan K i*
        (↑(g.val⁻¹) : Matrix GeckIndex GeckIndex K) := by
  rw [foldedImageAction_apply,cartanTensor_val]

theorem positive_eq_one_of_opposite_action_eq (K : Type) [Field K]
    (g h : foldedGroup K) (hg : g.val∈Positive K) (hh : h.val∈Negative K)
    (he : foldedImageAction K g=foldedImageAction K h) : g=1 := by
  have hp : g.val∈strictUnits ambientHeight :=
    positive_le_strict (CartanMatrix.D 4) (CartanMatrix.D_transpose 4) D4_positive_definite
      Base Index coordinateHeight (simple_height (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
        (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)) K hg
  have hn : h.val∈strictUnits (fun a=> -ambientHeight a) :=
    negative_le_strict_opposite (CartanMatrix.D 4) (CartanMatrix.D_transpose 4) D4_positive_definite
      Base Index coordinateHeight (simple_height (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
        (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)) K hh
  have hc (i : Fin 2) : Commute (g.val : Matrix GeckIndex GeckIndex K) (fieldCartan K i) := by
    have hv := congrArg (fun y : Image K=>y.val) (DFunLike.congr_fun he (cartanTensor K i))
    change (foldedImageAction K g (cartanTensor K i)).val =
      (foldedImageAction K h (cartanTensor K i)).val at hv
    rw [folded_action_cartan,folded_action_cartan] at hv
    have hd : (g.val : Matrix GeckIndex GeckIndex K)*fieldCartan K i*
        (↑(g.val⁻¹) : Matrix GeckIndex GeckIndex K)=fieldCartan K i := by
      simp only [fieldCartan_eq_diagonal] at hv ⊢
      exact opposite_equal_cartan_action_fixes ambientHeight g.val h.val hp hn
        (fun a : GeckIndex=>(cartanFunctional i (rootWeight a) : K)) hv
    have hm := congrArg (fun M : Matrix GeckIndex GeckIndex K=>M*(g.val : Matrix GeckIndex GeckIndex K)) hd
    simpa only [mul_assoc,Units.inv_mul,mul_one] using hm
  let u : Positive K := ⟨g.val,hg⟩
  have hu : u=1 := positive_cartan_centralizer_trivial K u hc
  apply Subtype.ext
  have hv := congrArg (fun z : Positive K=>z.val) hu
  change g.val=1 at hv
  exact hv

def positivePart (K : Type) [Field K] : Subgroup (foldedGroup K) :=
  (Positive K).subgroupOf (foldedGroup K)

def negativePart (K : Type) [Field K] : Subgroup (foldedGroup K) :=
  (Negative K).subgroupOf (foldedGroup K)

theorem foldedImageAction_injOn_positive (K : Type) [Field K] :
    Set.InjOn (foldedImageAction K) (positivePart K) := by
  intro g hg h hh he
  have hk : g*h⁻¹∈(foldedImageAction K).ker := by
    simp only [MonoidHom.mem_ker,map_mul,map_inv,he,mul_inv_cancel]
  have hu : (g*h⁻¹).val∈Positive K :=
    (Positive K).mul_mem hg ((Positive K).inv_mem hh)
  exact mul_inv_eq_one.mp (image_kernel_eq_one_of_positive K (g*h⁻¹) hk hu)

theorem opposite_action_images_disjoint (K : Type) [Field K] :
    (positivePart K).map (foldedImageAction K) ⊓
      (negativePart K).map (foldedImageAction K)=⊥ := by
  apply le_antisymm _ bot_le
  rintro x ⟨⟨g,hg,rfl⟩,h,hh,he⟩
  have hg1 := positive_eq_one_of_opposite_action_eq K g h hg hh he.symm
  simpa only [hg1,map_one,Subgroup.mem_bot]

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOppositeActionImages
