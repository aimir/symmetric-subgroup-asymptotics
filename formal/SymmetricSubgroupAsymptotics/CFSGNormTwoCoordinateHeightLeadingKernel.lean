import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateExactHeightWordLeading
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootHeightSupport

/-! Exact associated-height detection in the actual Geck matrix image-U:
inside the h-tail, vanishing of the height-h coefficient is equivalent
to membership in the (h+1)-tail, over EVERY field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHeightLeadingKernel
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGIntegerHeightSign
open CFSGNormTwoCoordinateRootBracketTransport CFSGNormTwoCoordinateRootCoefficientCoordinates
open CFSGNormTwoCoordinateRootHeightLeading CFSGNormTwoCoordinateRootHeightSupport
open CFSGNormTwoCoordinateRootHeightQuotient CFSGNormTwoCoordinateExactHeightLayer
open CFSGNormTwoCoordinateHeightLayerFactorization CFSGNormTwoCoordinateExactHeightWordLeading
open CFSGGradedMatrixSingleDegreeSpan CFSGGradedMatrixHighLayerProducts
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
private abbrev CoordMat (K : Type) := Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K

theorem factored_height_leading (K : Type) [Field K] (h : ℤ) (hh : 0<h)
    (c : ExactHeightRoot A h→K) (y : PositiveGroup A hd hs hp ho K)
    (hy : y∈heightTailInPositive A hd hs hp ho K (h+1)) :
    degreePart (heightWeight A hd hs hp ho) h
      ((((exactHeightWord A hd hs hp ho K h c*y).val : (CoordMat A hd hs hp ho K)ˣ) :
        CoordMat A hd hs hp ho K)-1)=
      ∑k,c k • selectedFieldCoefficient A hd hs hp ho K k.val.val := by
  have hw := exactHeightWord_cut_and_leading A hd hs hp ho K h hh c
  have hycut := heightTail_belowCut A hd hs hp ho K (h+1) (by omega) y.val hy
  have hyzero := heightTail_degreePart_zero A hd hs hp ho K (h+1) h
    (by omega) (by omega) y.val hy
  change degreePart (heightWeight A hd hs hp ho) h
    ((((exactHeightWord A hd hs hp ho K h c).val*y.val : (CoordMat A hd hs hp ho K)ˣ) :
      CoordMat A hd hs hp ho K)-1)=_
  rw [(leading_deviation_mul (heightWeight A hd hs hp ho) h hh
    (exactHeightWord A hd hs hp ho K h c).val y.val hw.1
    (belowCut_mono _ h (h+1) _ (by omega) hycut)).2,hyzero,add_zero]
  exact hw.2

theorem height_leading_zero_iff_next_tail (K : Type) [Field K] (h : ℤ) (hh : 0<h)
    (x : PositiveGroup A hd hs hp ho K) (hx : x∈heightTailInPositive A hd hs hp ho K h) :
    degreePart (heightWeight A hd hs hp ho) h ((x.val : CoordMat A hd hs hp ho K)-1)=0 ↔
      x∈heightTailInPositive A hd hs hp ho K (h+1) := by
  classical
  constructor
  · intro hz
    obtain ⟨c,y,hy,he⟩ := heightTailInPositive_factor A hd hs hp ho K h hh x hx
    rw [he,factored_height_leading A hd hs hp ho K h hh c y hy] at hz
    have hc : c=(fun _=>0) := root_family_coefficients_unique A hd hs hp ho K
      (fun k : ExactHeightRoot A h=>k.val.val)
      (fun _ _ h=>Subtype.ext (Subtype.ext h)) c (fun _=>0)
      (by simpa only [zero_smul,Finset.sum_const_zero] using hz)
    rw [hc,exactHeightWord_zero,one_mul] at he
    rw [he]
    exact hy
  · intro hxnext
    exact heightTail_degreePart_zero A hd hs hp ho K (h+1) h (by omega) (by omega) x.val hxnext

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHeightLeadingKernel
