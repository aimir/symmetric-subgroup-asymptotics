import SymmetricSubgroupAsymptotics.CFSGGradedMatrixCommutingFirstLayers
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLeadingFactor
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSimpleBracketDegrees
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCartan

/-! Nonzero first-layer parameters on adjacent simple axes cannot
commute in the SAME actual positive matrix group, in every field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateAdjacentLeadingNoncommute
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckHeightSupport
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckPositiveFirstLayer
open CFSGNormTwoCoordinateLeadingFactor CFSGNormTwoCoordinateHeight
open CFSGGradedMatrixGroupFirstLayer CFSGGradedMatrixCommutingFirstLayers
open CFSGNormTwoGeckSimpleBracketDegrees
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀
local notation "w" => weight A hs hp b₀ coordinateHeight
local notation "U" => rootGroup A hs hp b₀ s₀ K false

theorem firstLayer_of_leading_single (u : U) (i : Fin r) (a : K)
    (hu : leadingCoordinates A hd hs hp ho K u.val=(Pi.single i a : Fin r→K)) :
    firstLayer w u.val=a • fieldRoot D K false i := by
  classical
  rw [positive_firstLayer_eq_coordinates A hd hs hp ho K u.val u.property,hu]
  simp [Pi.single_apply]

theorem adjacent_leading_not_commute (u v : U) (i j : Fin r) (a b : K)
    (hij : A i j= -1) (ha : a≠0) (hb : b≠0)
    (hu : leadingCoordinates A hd hs hp ho K u.val=(Pi.single i a : Fin r→K))
    (hv : leadingCoordinates A hd hs hp ho K v.val=(Pi.single j b : Fin r→K)) :
    ¬Commute u v := by
  intro hc
  have hu' := (positive_firstLayer_mem_span A hs hp b₀ s₀ coordinateHeight
    (simple_height A hd hs hp ho) K u.val u.property).1
  have hv' := (positive_firstLayer_mem_span A hs hp b₀ s₀ coordinateHeight
    (simple_height A hd hs hp ho) K v.val v.property).1
  have hc' : Commute u.val v.val := congrArg Subtype.val hc.eq
  have hz := firstLayers_lie_eq_zero w u.val v.val hu' hv' hc'
  rw [firstLayer_of_leading_single A hd hs hp ho K u i a hu,
    firstLayer_of_leading_single A hd hs hp ho K v j b hv,
    smul_lie,lie_smul,smul_smul] at hz
  have hcartan : (b₀).cartanMatrix (s₀ j) (s₀ i)= -1 := by
    rw [CFSGNormTwoRootPairing.coordinate_cartan_transpose A hd hs hp ho]
    exact hij
  exact (smul_ne_zero (mul_ne_zero ha hb)
    (adjacent_bracket_ne_zero A hs hp b₀ s₀ K i j hcartan)) hz

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateAdjacentLeadingNoncommute
