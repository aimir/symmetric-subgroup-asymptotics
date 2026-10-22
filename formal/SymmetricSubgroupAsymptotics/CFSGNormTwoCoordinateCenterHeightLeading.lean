import SymmetricSubgroupAsymptotics.CFSGGradedMatrixLowestProduct
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHeightLeadingKernel
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckPositiveFirstLayer
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLeadingFactor
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixLieDegree
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixDistinctDegreeCoordinates

/-! At EVERY positive height, an actual element commuting with a simple
root has zero coordinate at every root raisable by that simple root.
Literal lattice-degree projection and the original integral unit bracket
make the conclusion valid in every characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCenterHeightLeading
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoGeckPositiveFirstLayer CFSGNormTwoGeckHeightSupport
open CFSGNormTwoCoordinateHeight CFSGNormTwoCoordinateLeadingFactor
open CFSGNormTwoCoordinateRootHeightLeading CFSGNormTwoCoordinateRootHeightSupport
open CFSGNormTwoCoordinateRootHeightQuotient CFSGNormTwoCoordinateExactHeightLayer
open CFSGNormTwoCoordinateHeightLayerFactorization CFSGNormTwoCoordinateHeightLeadingKernel
open CFSGNormTwoCoordinateRootBracketTransport CFSGNormTwoCoordinateRootCoefficientCoordinates
open CFSGGradedMatrixLowestProduct CFSGGradedMatrixHighLayerProducts
open CFSGGradedMatrixSingleDegreeSpan CFSGGradedMatrixGroupFirstLayer
open CFSGGradedMatrixLieFirstLayer CFSGGradedMatrixLieDegree
open CFSGGradedMatrixDistinctDegreeCoordinates CFSGGradedMatrixSupport
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀
local notation "ell" => latticeWeight A hs hp b₀
private abbrev CoordMat (K : Type) := Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K

theorem canonical_simple_height_leading (K : Type) [Field K] (i : Fin r) :
    BelowCut (heightWeight A hd hs hp ho) 1
      ((canonicalRoot D K false i 1 : CoordMat A hd hs hp ho K)-1) ∧
      degreePart (heightWeight A hd hs hp ho) 1
        ((canonicalRoot D K false i 1 : CoordMat A hd hs hp ho K)-1)=fieldRoot D K false i := by
  have hweight : weight A hs hp b₀ coordinateHeight=heightWeight A hd hs hp ho := by
    funext j
    rcases j with j|j
    · simp [weight,heightWeight,latticeWeight,CFSGIntegerHeightSign.height]
    · rfl
  have hc := simple_strict A hs hp b₀ s₀ coordinateHeight (simple_height A hd hs hp ho) K i 1
  rw [hweight] at hc
  constructor
  · intro j k hjk
    change (canonicalRoot D K false i 1 : CoordMat A hd hs hp ho K) j k-
      (1 : CoordMat A hd hs hp ho K) j k=0
    exact sub_eq_zero.mpr (hc j k (by
      change heightWeight A hd hs hp ho j≤heightWeight A hd hs hp ho k
      omega))
  · have hf := simple_firstLayer A hs hp b₀ s₀ coordinateHeight (simple_height A hd hs hp ho) K i 1
    rw [hweight] at hf
    simpa only [firstLayer,firstPart,one_smul] using hf

theorem lowest_bracket_zero_of_commutes (K : Type) [Field K] (h : ℤ) (hh : 0<h)
    (u : PositiveGroup A hd hs hp ho K) (hu : u∈heightTailInPositive A hd hs hp ho K h)
    (i : Fin r)
    (hc : u.val*canonicalRoot D K false i 1=canonicalRoot D K false i 1*u.val) :
    ⁅fieldRoot D K false i,
      degreePart (heightWeight A hd hs hp ho) h ((u.val : CoordMat A hd hs hp ho K)-1)⁆=0 := by
  have hsimp := canonical_simple_height_leading A hd hs hp ho K i
  have hpart := commuting_units_lowest_parts (heightWeight A hd hs hp ho) h 1
    u.val (canonicalRoot D K false i 1)
    (heightTail_belowCut A hd hs hp ho K h hh u.val hu) hsimp.1 hc
  rw [hsimp.2] at hpart
  exact sub_eq_zero.mpr hpart.symm

theorem raisable_height_coordinate_zero (K : Type) [Field K] (h : ℤ) (hh : 0<h)
    (u : PositiveGroup A hd hs hp ho K)
    (c : ExactHeightRoot A h→K) (y : PositiveGroup A hd hs hp ho K)
    (hy : y∈heightTailInPositive A hd hs hp ho K (h+1))
    (he : u=exactHeightWord A hd hs hp ho K h c*y)
    (hu : u∈heightTailInPositive A hd hs hp ho K h) (i : Fin r)
    (hc : u.val*canonicalRoot D K false i 1=canonicalRoot D K false i 1*u.val)
    (k : ExactHeightRoot A h)
    (hpair : integerPairing A k.val.val.val (s₀ i : Roots A).val= -1) : c k=0 := by
  classical
  have hbr := lowest_bracket_zero_of_commutes A hd hs hp ho K h hh u hu i hc
  rw [he,factored_height_leading A hd hs hp ho K h hh c y hy] at hbr
  have hsum : (∑l : ExactHeightRoot A h,c l •
      ⁅fieldRoot D K false i,selectedFieldCoefficient A hd hs hp ho K l.val.val⁆)=0 := by
    simpa only [lie_sum,lie_smul] using hbr
  let d : ExactHeightRoot A h→Fin r→ℤ := fun l=>(s₀ i : Roots A).val+l.val.val.val
  have hdinj : Function.Injective d := by
    intro a b hab
    exact Subtype.ext (Subtype.ext (Subtype.ext (add_left_cancel hab)))
  have hpj := congrArg (degreePart ell (d k)) hsum
  rw [degreePart_sum ell d hdinj
    (fun l=>⁅fieldRoot D K false i,selectedFieldCoefficient A hd hs hp ho K l.val.val⁆)
    (fun l=>supported_lie ell (s₀ i : Roots A).val l.val.val.val _ _
      (field_E_lattice_support A hs hp b₀ s₀ K i)
      (selectedFieldCoefficient_support A hd hs hp ho K l.val.val)) c k,map_zero] at hpj
  obtain ⟨ε,hε,hεeq⟩ := all_ring_simple_root_bracket_sign A hd hs hp ho
    k.val.val k.val.property i hpair
  have hn : ⁅fieldRoot D K false i,selectedFieldCoefficient A hd hs hp ho K k.val.val⁆≠0 := by
    rw [hεeq K]
    apply smul_ne_zero
    · rcases hε with rfl|rfl <;> norm_num
    · exact selectedFieldCoefficient_ne_zero A hd hs hp ho K _
  exact (smul_eq_zero.mp hpj).resolve_right hn

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCenterHeightLeading
