import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticImageDegreeTwo
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSingleRootAdjoint
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckGeneratedLieInvariance
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNegativeQuadraticGrade
import SymmetricSubgroupAsymptotics.CFSGGeckSerreImage

/-! Individual ORIGINAL Serre root operators have degree two on their
SAME coordinate Geck integral image. The rational cube is discharged by
actual generated-Lie membership and root degree; every mapped integral
divided power of degree at least three then vanishes in every ring. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateImageDegreeTwo
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckLatticeDegree CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckColumns
open CFSGNormTwoGeckGeneratedLieInvariance CFSGNormTwoGeckNegativeQuadraticGrade
open CFSGSerreQuadraticMatrix CFSGGradedMatrixSupport
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀
local notation "C" => CFSGGeckSerreRepresentation.cartan b₀ s₀
local notation "ell" => latticeWeight A hs hp b₀

theorem rational_image_ad_cube (neg : Bool) (i : Fin r) (x : RationalLie C) :
    ⁅fieldRoot D ℚ neg i,⁅fieldRoot D ℚ neg i,⁅fieldRoot D ℚ neg i,(D).rational x⁆⁆⁆=0 := by
  have hx := CFSGGeckSerreImage.rationalRepresentation_mem_lieAlgebra b₀ s₀ x
  cases neg
  · exact CFSGNormTwoCoordinateSingleRootAdjoint.single_root_ad_cube A hd hs hp ho
      (s₀ i) (fieldRoot D ℚ false i) (root_mem_generated A hs hp b₀ s₀ false i)
      (field_E_lattice_support A hs hp b₀ s₀ ℚ i) ((D).rational x) hx
  · have hF : Supported ell (fun v=>v+(negativeIndex A hs hp (s₀ i)).val)
        (fieldRoot D ℚ true i) := by
      simpa only [negative_val,sub_eq_add_neg] using field_F_support A hs hp b₀ s₀ ℚ i
    exact CFSGNormTwoCoordinateSingleRootAdjoint.single_root_ad_cube A hd hs hp ho
      (negativeIndex A hs hp (s₀ i)) (fieldRoot D ℚ true i)
      (root_mem_generated A hs hp b₀ s₀ true i) hF ((D).rational x) hx

theorem integral_original_operator_ge_three (neg : Bool) (i : Fin r) (k : ℕ) (hk : 3≤k)
    (x : integralLattice C) : integralRepresentation D (integralOperator C neg i k x)=0 :=
  integral_image_operator_ge_three D (rational_image_ad_cube A hd hs hp ho) neg i k hk x

theorem all_ring_image_operator_ge_three (K : Type*) [CommRing K]
    (neg : Bool) (i : Fin r) (k : ℕ) (hk : 3≤k) (x : K⊗[ℤ]integralLattice C) :
    CFSGIntegralQuadraticRootOperators.operator K (fieldRoot D K neg i)
      (fieldSecond D K neg i) k (baseChange D K x)=0 :=
  baseChange_image_operator_ge_three D (rational_image_ad_cube A hd hs hp ho) K neg i k hk x

theorem original_rootOperator_degree_two (K : Type) [Field K]
    (neg : Bool) (i : Fin r) (t : K) (x : Space C K) :
    baseChange D K (rootOperator C K neg i t x)=baseChange D K x+
      t • CFSGIntegralQuadraticRootOperators.operator K (fieldRoot D K neg i)
        (fieldSecond D K neg i) 1 (baseChange D K x)+
      t^2 • CFSGIntegralQuadraticRootOperators.operator K (fieldRoot D K neg i)
        (fieldSecond D K neg i) 2 (baseChange D K x) :=
  baseChange_rootOperator_degree_two D (rational_image_ad_cube A hd hs hp ho) K neg i t x

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateImageDegreeTwo
