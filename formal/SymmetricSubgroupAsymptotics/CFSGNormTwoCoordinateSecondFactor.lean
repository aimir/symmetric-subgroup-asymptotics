import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDerivedSecondLayer
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrderedCommutatorFactor
import Mathlib.Data.Fintype.BigOperators

/-! Actual height-two collection in the original coordinate positive
group. Ordered literal simple commutators remove the whole second layer;
the remainder stays in the SAME U and has height at least three. The
ordered-pair parameters are redundant, so no uniqueness is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSecondFactor
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckHeightSupport
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckPositiveFirstLayer
open CFSGNormTwoCoordinateHeight CFSGNormTwoCoordinateDerivedFirstLayer
open CFSGNormTwoCoordinateDerivedSecondLayer CFSGNormTwoGeckOrderedCommutatorFactor
open CFSGGradedMatrixGroupFirstLayer CFSGGradedMatrixGroupSecondLayer
open CFSGGradedMatrixDerivedSecondLayer CFSGGradedMatrixOrderedSecondLayer
open CFSGGradedMatrixSubgroups
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀
local notation "w" => weight A hs hp b₀ coordinateHeight
local notation "U" => rootGroup A hs hp b₀ s₀ K false

theorem derived_ordered_second_factor (u : U) (hu : u∈commutator U) :
    ∃ (c : Fin r→Fin r→K) (v : U),
      (∀i j,w i≤w j+2→
        (v.val : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K) i j=
          (1 : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K) i j) ∧
      u.val=v.val*orderedCommutators A hs hp b₀ s₀ K c := by
  have hspan := derived_secondLayer_mem A hd hs hp ho K u hu
  change secondLayer w u.val∈Submodule.span K
    (Set.range (fun p : Fin r×Fin r=>
      ⁅fieldRoot D K false p.1,fieldRoot D K false p.2⁆)) at hspan
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hspan
  let c' : Fin r→Fin r→K := fun i j=>c (i,j)
  have hcoeff : (∑i,∑j,c' i j • ⁅fieldRoot D K false i,fieldRoot D K false j⁆)=
      secondLayer w u.val := by
    simpa only [Fintype.sum_prod_type,c'] using hc
  let q := orderedCommutators A hs hp b₀ s₀ K c'
  have hq : q∈U := orderedCommutators_mem_positive A hs hp b₀ s₀ K c'
  have hqLayers := orderedCommutators_layers A hs hp b₀ s₀ coordinateHeight
    (simple_height A hd hs hp ho) K c'
  have huStrict := (positive_firstLayer_mem_span A hs hp b₀ s₀ coordinateHeight
    (simple_height A hd hs hp ho) K u.val u.property).1
  have hu0 := (firstLayer_zero_iff_mem_derived A hd hs hp ho K u).mpr hu
  have hq0 : firstLayer w q=0 := hqLayers.2.1
  have hqSecond : secondLayer w q=secondLayer w u.val := hqLayers.2.2.trans hcoeff
  let v : U := ⟨u.val*q⁻¹,(U).mul_mem u.property ((U).inv_mem hq)⟩
  have hvStrict : v.val∈strictUnits w :=
    (strictUnits w).mul_mem huStrict ((strictUnits w).inv_mem hqLayers.1)
  have hv0 : firstLayer w v.val=0 := by
    change firstLayer w (u.val*q⁻¹)=0
    rw [firstLayer_mul w u.val q⁻¹ huStrict ((strictUnits w).inv_mem hqLayers.1),
      firstLayer_inv w q hqLayers.1,hu0,hq0,neg_zero,add_zero]
  have hvSecond : secondLayer w v.val=0 :=
    matching_secondLayer_correction w u.val q huStrict hqLayers.1 hu0 hq0 hqSecond.symm
  refine ⟨c',v,height_three_of_secondLayer_zero w v.val hvStrict hv0 hvSecond,?_⟩
  change u.val=(u.val*q⁻¹)*q
  simp only [mul_assoc,inv_mul_cancel,mul_one]

theorem height_two_ordered_second_factor (u : U)
    (hhigh : ∀i j,w i≤w j+1→
      (u.val : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K) i j=
        (1 : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K) i j) :
    ∃ (c : Fin r→Fin r→K) (v : U),
      (∀i j,w i≤w j+2→
        (v.val : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K) i j=
          (1 : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K) i j) ∧
      u.val=v.val*orderedCommutators A hs hp b₀ s₀ K c :=
  derived_ordered_second_factor A hd hs hp ho K u
    ((height_two_iff_mem_derived A hd hs hp ho K u).mp hhigh)

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSecondFactor
