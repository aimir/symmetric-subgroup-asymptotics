import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootHeightLeading
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootHeightFiltration
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! EVERY element of the actual h-tail has no matrix coefficient below
height h. Generator inverses are the same actual root with negative
parameter, so this proof requires no unproved inverse-closure assertion. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootHeightSupport
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGIntegerHeightSign
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateRootHeightLeading
open CFSGNormTwoCoordinateRootHeightFiltration CFSGGradedMatrixHighLayerProducts
open CFSGGradedMatrixSingleDegreeSpan
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
private abbrev CoordMat (K : Type) := Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K

theorem selected_root_belowCut (K : Type) [Field K] (h : ℤ) (hh : 0<h)
    (k : Roots A) (hk : h≤height k.val) (a : K) :
    BelowCut (heightWeight A hd hs hp ho) h
      ((selectedRootElement A hd hs hp ho K k a : CoordMat A hd hs hp ho K)-1) :=
  belowCut_mono (heightWeight A hd hs hp ho) h (height k.val) _ hk
    (selected_root_cut_and_leading A hd hs hp ho K k (lt_of_lt_of_le hh hk) a).1

theorem heightTail_belowCut (K : Type) [Field K] (h : ℤ) (hh : 0<h)
    (x : (CoordMat A hd hs hp ho K)ˣ) (hx : x∈heightTail A hd hs hp ho K h) :
    BelowCut (heightWeight A hd hs hp ho) h ((x : CoordMat A hd hs hp ho K)-1) := by
  apply Subgroup.closure_induction'' (p:=fun x _=>
    BelowCut (heightWeight A hd hs hp ho) h ((x : CoordMat A hd hs hp ho K)-1))
    (s:=heightRootGenerators A hd hs hp ho K h) ?_ ?_ ?_ ?_ hx
  · rintro x ⟨k,hk,a,rfl⟩
    exact selected_root_belowCut A hd hs hp ho K h hh k.val hk a
  · rintro x ⟨k,hk,a,rfl⟩
    rw [selectedRootElement_inverse]
    exact selected_root_belowCut A hd hs hp ho K h hh k.val hk (-a)
  · intro i j hij
    simp only [Units.val_one,sub_self,Matrix.zero_apply]
  · intro x y hx hy hxc hyc
    exact (leading_deviation_mul (heightWeight A hd hs hp ho) h hh x y hxc hyc).1

theorem heightTail_degreePart_zero (K : Type) [Field K] (h d : ℤ) (hh : 0<h) (hdh : d<h)
    (x : (CoordMat A hd hs hp ho K)ˣ) (hx : x∈heightTail A hd hs hp ho K h) :
    degreePart (heightWeight A hd hs hp ho) d ((x : CoordMat A hd hs hp ho K)-1)=0 := by
  have hc := heightTail_belowCut A hd hs hp ho K h hh x hx
  apply Matrix.ext
  intro i j
  change (if heightWeight A hd hs hp ho i=heightWeight A hd hs hp ho j+d
    then ((x : CoordMat A hd hs hp ho K)-1) i j else 0)=0
  split_ifs with he
  · exact hc i j (by omega)
  · rfl

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootHeightSupport
