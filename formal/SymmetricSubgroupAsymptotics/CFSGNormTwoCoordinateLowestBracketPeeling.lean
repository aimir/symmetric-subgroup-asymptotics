import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCentralHeightFactor
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLowestBracketRaise
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateExactHeightWordLeading

/-! Vanishing simple brackets of the actual lowest part remove every
non-dominant parameter. Below the dominant height this advances the
literal height filtration without requiring ambient-U centrality. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLowestBracketPeeling
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGIntegerHeightSign
open CFSGNormTwoCoordinateRootHeightQuotient CFSGNormTwoCoordinateExactHeightLayer
open CFSGNormTwoCoordinateHeightLayerFactorization CFSGNormTwoCoordinateHighestRoot
open CFSGNormTwoCoordinateDominantRootUnique CFSGNormTwoCoordinateLowestBracketRaise
open CFSGNormTwoCoordinateExactHeightWordLeading CFSGNormTwoGeckIntegralRealization
open CFSGGradedMatrixSingleDegreeSpan CFSGNormTwoCoordinateHeight CFSGSerreQuadraticMatrix
open CFSGNormTwoCoordinateRootHeightLeading
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀
private abbrev CoordMat (K : Type) := Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K

theorem parameters_vanish_off_dominant (K : Type) [Field K]
    (θ : Roots A) (hθ : ∀i,0≤θ.val i)
    (hdom : ∀i,0 ≤ integerPairing A θ.val (Pi.single i (1:ℤ) : Fin r→ℤ))
    (h : ℤ) (hh : 0<h) (u : PositiveGroup A hd hs hp ho K)
    (hbr : ∀i, ⁅fieldRoot D K false i,
      degreePart (heightWeight A hd hs hp ho) h ((u.val : CoordMat A hd hs hp ho K)-1)⁆=0)
    (c : ExactHeightRoot A h→K) (y : PositiveGroup A hd hs hp ho K)
    (hy : y∈heightTailInPositive A hd hs hp ho K (h+1))
    (he : u=exactHeightWord A hd hs hp ho K h c*y) :
    ∀k : ExactHeightRoot A h,k.val.val≠θ→c k=0 := by
  classical
  intro k hk
  have hndom : ¬∀i,0 ≤ integerPairing A k.val.val.val (Pi.single i (1:ℤ) : Fin r→ℤ) := by
    intro hkdom
    exact hk (dominant_positive_root_unique A hd hs hp ho k.val.val θ
      k.val.property hθ hkdom hdom)
  obtain ⟨i,hi⟩ := not_forall.mp hndom
  have hpair := negative_simple_pairing_eq_neg_one A hd hs hp ho k.val.val k.val.property i
    (lt_of_not_ge hi)
  exact raisable_coordinate_zero_of_lowest_bracket_zero A hd hs hp ho K h hh u c y hy he
    i (hbr i) k hpair

theorem mem_next_tail_of_lowest_brackets_zero (K : Type) [Field K]
    (θ : Roots A) (hθ : ∀i,0≤θ.val i)
    (hdom : ∀i,0 ≤ integerPairing A θ.val (Pi.single i (1:ℤ) : Fin r→ℤ))
    (h : ℤ) (hh : 0<h) (hne : h≠height θ.val)
    (u : PositiveGroup A hd hs hp ho K)
    (hu : u∈heightTailInPositive A hd hs hp ho K h)
    (hbr : ∀i, ⁅fieldRoot D K false i,
      degreePart (heightWeight A hd hs hp ho) h ((u.val : CoordMat A hd hs hp ho K)-1)⁆=0) :
    u∈heightTailInPositive A hd hs hp ho K (h+1) := by
  obtain ⟨c,y,hy,he⟩ := heightTailInPositive_factor A hd hs hp ho K h hh u hu
  have hc := parameters_vanish_off_dominant A hd hs hp ho K θ hθ hdom h hh u hbr c y hy he
  have hc0 : c=(fun _=>0) := by
    funext k
    apply hc k
    intro hk
    have hheight : height k.val.val.val=height θ.val := congrArg (fun a : Roots A=>height a.val) hk
    exact hne (k.property.symm.trans hheight)
  rw [hc0,exactHeightWord_zero,one_mul] at he
  exact he.symm ▸ hy

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLowestBracketPeeling
