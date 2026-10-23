import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCenterHeightLeading

/-! The actual unit-bracket height elimination needs only a vanishing
lowest Lie bracket; full commutation with an individual root group is
unnecessary. This form permits folded-field tests. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLowestBracketRaise
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckLatticeDegree
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


theorem raisable_coordinate_zero_of_lowest_bracket_zero (K : Type) [Field K]
    (h : ℤ) (hh : 0<h) (u : PositiveGroup A hd hs hp ho K)
    (c : ExactHeightRoot A h→K) (y : PositiveGroup A hd hs hp ho K)
    (hy : y∈heightTailInPositive A hd hs hp ho K (h+1))
    (he : u=exactHeightWord A hd hs hp ho K h c*y) (i : Fin r)
    (hbr : ⁅fieldRoot D K false i,
      degreePart (heightWeight A hd hs hp ho) h ((u.val : CoordMat A hd hs hp ho K)-1)⁆=0)
    (k : ExactHeightRoot A h)
    (hpair : integerPairing A k.val.val.val (s₀ i : Roots A).val= -1) : c k=0 := by
  classical
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


end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLowestBracketRaise
