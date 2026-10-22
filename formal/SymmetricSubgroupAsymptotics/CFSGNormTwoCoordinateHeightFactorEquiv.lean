import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHeightFactorUniqueness
import Mathlib.Algebra.Group.Subgroup.Finite

/-! Exact one-step factor equivalence and cardinal recursion for the
ACTUAL positive-root height filtration. The layer is the full parameter
space, with no good-characteristic or root-factorization hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHeightFactorEquiv
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCoordinateRootHeightQuotient CFSGNormTwoCoordinateRootHeightFiltration
open CFSGNormTwoCoordinateExactHeightLayer CFSGNormTwoCoordinateHeightLayerFactorization
open CFSGNormTwoCoordinateExactHeightWordLeading CFSGNormTwoCoordinateHeightFactorUniqueness
open CFSGFiniteQuotientFamilyProduct
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

theorem exactHeightWord_mem_tail (K : Type) [Field K] (h : ℤ) (c : ExactHeightRoot A h→K) :
    exactHeightWord A hd hs hp ho K h c∈heightTailInPositive A hd hs hp ho K h := by
  classical
  change (exactHeightWord A hd hs hp ho K h c).val∈heightTail A hd hs hp ho K h
  rw [exactHeightWord_coe,orderedFamilyProduct]
  apply (heightTail A hd hs hp ho K h).list_prod_mem
  intro x hx
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp hx
  exact rootElement_mem_heightTail A hd hs hp ho K h k.val.val k.val.property
    (le_of_eq k.property.symm) (c k)

def heightFactorMap (K : Type) [Field K] (h : ℤ) :
    ((ExactHeightRoot A h→K) × heightTailInPositive A hd hs hp ho K (h+1))→
      heightTailInPositive A hd hs hp ho K h := fun p=>
  ⟨exactHeightWord A hd hs hp ho K h p.1*p.2.val,
    (heightTailInPositive A hd hs hp ho K h).mul_mem
      (exactHeightWord_mem_tail A hd hs hp ho K h p.1)
      (heightTail_antitone A hd hs hp ho K (by omega : h≤h+1) p.2.property)⟩

def heightFactorEquiv (K : Type) [Field K] (h : ℤ) (hh : 0<h) :
    ((ExactHeightRoot A h→K) × heightTailInPositive A hd hs hp ho K (h+1)) ≃
      heightTailInPositive A hd hs hp ho K h :=
  Equiv.ofBijective (heightFactorMap A hd hs hp ho K h) (by
    constructor
    · intro x y he
      apply height_factor_injective A hd hs hp ho K h hh
      exact congrArg Subtype.val he
    · intro x
      obtain ⟨c,y,hy,he⟩ := heightTailInPositive_factor A hd hs hp ho K h hh x.val x.property
      refine ⟨(c,⟨y,hy⟩),?_⟩
      apply Subtype.ext
      exact he.symm)

theorem heightTail_card_step (K : Type) [Field K] (h : ℤ) (hh : 0<h) :
    Nat.card (heightTailInPositive A hd hs hp ho K h)=
      Nat.card K ^ Nat.card (ExactHeightRoot A h) *
        Nat.card (heightTailInPositive A hd hs hp ho K (h+1)) := by
  have he := (Nat.card_congr (heightFactorEquiv A hd hs hp ho K h hh)).symm
  simpa only [Nat.card_prod,Nat.card_fun] using he

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHeightFactorEquiv
