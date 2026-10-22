import SymmetricSubgroupAsymptotics.CFSGFiniteLayerCollection
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHeightLayerFactorization
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootHeightBound
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootElementRange

/-! SURJECTIVE finite ordered-height collection for the literal Geck
MATRIX image-U. Every parameter is an actual selected root parameter.
Uniqueness and original Serre/projective transfer are separate tasks. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveHeightNormalForm
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGIntegerHeightSign
open CFSGNormTwoCoordinatePositiveRootGenerators CFSGNormTwoCoordinateRootHeightFiltration
open CFSGNormTwoCoordinateRootHeightQuotient CFSGNormTwoCoordinateRootHeightCommutator
open CFSGNormTwoCoordinateRootHeightBound CFSGNormTwoCoordinateRootElementRange
open CFSGNormTwoCoordinateExactHeightLayer CFSGNormTwoCoordinateHeightLayerFactorization
open CFSGFiniteLayerCollection

variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

theorem heightTail_one_eq_positive (K : Type) [Field K] :
    heightTail A hd hs hp ho K 1=PositiveGroup A hd hs hp ho K := by
  apply le_antisymm (heightTail_le_positive A hd hs hp ho K 1)
  rw [positive_group_eq_iSup]
  apply iSup_le
  intro k x hx
  obtain ⟨a,rfl⟩ := (mem_rootSubgroup_iff_selected A hd hs hp ho K k.val x).mp hx
  exact rootElement_mem_heightTail A hd hs hp ho K 1 k.val k.property
    (by have hh := positive_root_height_pos A k.val k.property;omega) a

def positiveHeightNormalWord (K : Type) [Field K]
    (c : ∀n : ℕ,ExactHeightRoot A ((n:ℤ)+1)→K) : PositiveGroup A hd hs hp ho K :=
  ((List.range (rootHeightBound A)).map
    (fun n : ℕ=>exactHeightWord A hd hs hp ho K ((n:ℤ)+1) (c n))).prod

theorem positiveHeightNormalWord_surjective (K : Type) [Field K] :
    Function.Surjective (positiveHeightNormalWord A hd hs hp ho K) := by
  classical
  intro x
  let N : ℕ→Subgroup (PositiveGroup A hd hs hp ho K) :=
    fun n=>heightTailInPositive A hd hs hp ho K ((n:ℤ)+1)
  let C : ℕ→Type := fun n=>ExactHeightRoot A ((n:ℤ)+1)→K
  let w : ∀n,C n→PositiveGroup A hd hs hp ho K :=
    fun n=>exactHeightWord A hd hs hp ho K ((n:ℤ)+1)
  have hstep : ∀n,∀y∈N n,∃c : C n,∃z∈N (n+1),y=w n c*z := by
    intro n y hy
    have hn : (((n+1:ℕ):ℤ)+1)=(n:ℤ)+1+1 := by omega
    simpa only [N,C,w,hn] using
      heightTailInPositive_factor A hd hs hp ho K ((n:ℤ)+1) (by omega) y hy
  have hx : x∈N 0 := by
    change x.val∈heightTail A hd hs hp ho K 1
    rw [heightTail_one_eq_positive]
    exact x.property
  have hfinal : N (rootHeightBound A)=⊥ := by
    change (heightTail A hd hs hp ho K ((rootHeightBound A:ℤ)+1)).subgroupOf
      (PositiveGroup A hd hs hp ho K)=⊥
    rw [final_heightTail_eq_bot,Subgroup.bot_subgroupOf]
  obtain ⟨c,hc⟩ := collect_when_final_bot N C w hstep x hx (rootHeightBound A) hfinal
  refine ⟨c,?_⟩
  simpa only [positiveHeightNormalWord,w] using hc.symm

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveHeightNormalForm
