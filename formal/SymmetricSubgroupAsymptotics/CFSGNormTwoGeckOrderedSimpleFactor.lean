import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckPositiveFirstLayer
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixOrderedFirstLayer
import Mathlib.Algebra.Group.Submonoid.BigOperators

/-! An actual positive-group element admits its ordered SIMPLE-root
leading factor, with a height-at-least-two remainder still in the same U.
No full ordered-root factorization or Sylow-centre claim is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrderedSimpleFactor
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckHeightSupport
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckPositiveFirstLayer
open CFSGGradedMatrixGroupFirstLayer CFSGGradedMatrixOrderedFirstLayer
open CFSGGradedMatrixSubgroups
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)
    (height : (n→ℤ)→ₗ[ℤ]ℤ) (hheight : ∀i : b.support,height (i:Roots A).val=1)

local notation "D" => realizationData A hs hp b s
local notation "w" => weight A hs hp b height

def orderedSimple (K : Type) [Field K] (c : Fin r→K) :
    (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ :=
  (List.ofFn (fun i : Fin r=>canonicalRoot D K false i (c i))).prod

theorem orderedSimple_mem_positive (K : Type) [Field K] (c : Fin r→K) :
    orderedSimple A hs hp b s K c∈rootGroup A hs hp b s K false := by
  apply _root_.list_prod_mem
  intro u hu
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hu
  exact Subgroup.subset_closure ⟨(i,c i),rfl⟩

include hheight in
theorem orderedSimple_firstLayer (K : Type) [Field K] (c : Fin r→K) :
    firstLayer w (orderedSimple A hs hp b s K c)=∑i,c i • fieldRoot D K false i := by
  have hl := list_product_firstLayer w
    (List.ofFn (fun i : Fin r=>canonicalRoot D K false i (c i))) (by
      intro u hu
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hu
      exact simple_strict A hs hp b s height hheight K i (c i))
  simpa only [orderedSimple,List.map_ofFn,List.sum_ofFn,Function.comp_apply,
    simple_firstLayer A hs hp b s height hheight] using hl.2

include hheight in
theorem exists_ordered_simple_factor (K : Type) [Field K]
    (u : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ)
    (hu : u∈rootGroup A hs hp b s K false) :
    ∃ (c : Fin r→K) (v : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ),
      v∈rootGroup A hs hp b s K false ∧
      (∀i j,w i≤w j+1→(v : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K) i j=
        (1 : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K) i j) ∧
      u=v*orderedSimple A hs hp b s K c := by
  obtain ⟨c,hc⟩ := exists_leading_coefficients A hs hp b s height hheight K u hu
  let q := orderedSimple A hs hp b s K c
  have hq : q∈rootGroup A hs hp b s K false := orderedSimple_mem_positive A hs hp b s K c
  have hu' := (positive_firstLayer_mem_span A hs hp b s height hheight K u hu).1
  have hq' := (positive_firstLayer_mem_span A hs hp b s height hheight K q hq).1
  refine ⟨c,u*q⁻¹,(rootGroup A hs hp b s K false).mul_mem hu
    ((rootGroup A hs hp b s K false).inv_mem hq),?_,?_⟩
  · apply height_two_of_firstLayer_zero w (u*q⁻¹)
      ((strictUnits w).mul_mem hu' ((strictUnits w).inv_mem hq'))
    apply matching_firstLayer_correction w u q hu' hq'
    rw [orderedSimple_firstLayer A hs hp b s height hheight]
    exact hc.symm
  · change u=(u*q⁻¹)*q
    simp only [mul_assoc,inv_mul_cancel,mul_one]

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrderedSimpleFactor
