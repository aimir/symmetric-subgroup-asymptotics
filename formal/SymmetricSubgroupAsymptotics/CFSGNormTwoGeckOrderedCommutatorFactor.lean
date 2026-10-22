import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSimpleCommutatorLayer
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixOrderedSecondLayer
import Mathlib.Algebra.Group.Submonoid.BigOperators

/-! Ordered literal simple commutators realize arbitrary linear
combinations of the simple brackets in height two. Redundant ordered-pair
parameters are intentional; no uniqueness is asserted here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrderedCommutatorFactor
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckHeightSupport
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckPositiveFirstLayer
open CFSGNormTwoGeckSimpleCommutatorLayer CFSGGradedMatrixOrderedSecondLayer
open CFSGGradedMatrixGroupFirstLayer CFSGGradedMatrixGroupSecondLayer
open CFSGGradedMatrixSubgroups
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

local notation "D" => realizationData A hs hp b s

def orderedCommutatorRow (K : Type) [Field K] (c : Fin r→Fin r→K) (i : Fin r) :
    (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ :=
  (List.ofFn (fun j : Fin r=>simpleCommutator A hs hp b s K i j (c i j))).prod

def orderedCommutators (K : Type) [Field K] (c : Fin r→Fin r→K) :
    (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ :=
  (List.ofFn (fun i : Fin r=>orderedCommutatorRow A hs hp b s K c i)).prod

theorem orderedCommutatorRow_mem_positive (K : Type) [Field K]
    (c : Fin r→Fin r→K) (i : Fin r) :
    orderedCommutatorRow A hs hp b s K c i∈rootGroup A hs hp b s K false := by
  apply _root_.list_prod_mem
  intro u hu
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hu
  exact simpleCommutator_mem_positive A hs hp b s K i j (c i j)

theorem orderedCommutators_mem_positive (K : Type) [Field K] (c : Fin r→Fin r→K) :
    orderedCommutators A hs hp b s K c∈rootGroup A hs hp b s K false := by
  apply _root_.list_prod_mem
  intro u hu
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hu
  exact orderedCommutatorRow_mem_positive A hs hp b s K c i

variable (height : (n→ℤ)→ₗ[ℤ]ℤ) (hheight : ∀i : b.support,height (i:Roots A).val=1)
include hheight
local notation "w" => weight A hs hp b height

theorem orderedCommutatorRow_layers (K : Type) [Field K]
    (c : Fin r→Fin r→K) (i : Fin r) :
    orderedCommutatorRow A hs hp b s K c i∈strictUnits w ∧
      firstLayer w (orderedCommutatorRow A hs hp b s K c i)=0 ∧
      secondLayer w (orderedCommutatorRow A hs hp b s K c i)=
        ∑j,c i j • ⁅fieldRoot D K false i,fieldRoot D K false j⁆ := by
  have hl := list_product_secondLayer w
    (List.ofFn (fun j : Fin r=>simpleCommutator A hs hp b s K i j (c i j))) (by
      intro u hu
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hu
      exact ⟨(positive_firstLayer_mem_span A hs hp b s height hheight K _
        (simpleCommutator_mem_positive A hs hp b s K i j (c i j))).1,
        simpleCommutator_firstLayer A hs hp b s height hheight K i j (c i j)⟩)
  simpa only [orderedCommutatorRow,List.map_ofFn,List.sum_ofFn,Function.comp_apply,
    simpleCommutator_secondLayer A hs hp b s height hheight] using hl

theorem orderedCommutators_layers (K : Type) [Field K] (c : Fin r→Fin r→K) :
    orderedCommutators A hs hp b s K c∈strictUnits w ∧
      firstLayer w (orderedCommutators A hs hp b s K c)=0 ∧
      secondLayer w (orderedCommutators A hs hp b s K c)=
        ∑i,∑j,c i j • ⁅fieldRoot D K false i,fieldRoot D K false j⁆ := by
  have hl := list_product_secondLayer w
    (List.ofFn (fun i : Fin r=>orderedCommutatorRow A hs hp b s K c i)) (by
      intro u hu
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hu
      have hi := orderedCommutatorRow_layers A hs hp b s height hheight K c i
      exact ⟨hi.1,hi.2.1⟩)
  refine ⟨hl.1,hl.2.1,?_⟩
  change secondLayer w
    (List.ofFn (fun i : Fin r=>orderedCommutatorRow A hs hp b s K c i)).prod=_
  rw [hl.2.2]
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  apply Finset.sum_congr rfl
  intro i hi
  exact (orderedCommutatorRow_layers A hs hp b s height hheight K c i).2.2

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrderedCommutatorFactor
