import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDerivedFirstLayer
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixCommutatorSecondLayer
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixDistinctDegreeCoordinates
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSimpleBracketDegrees
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCartan
import Mathlib.GroupTheory.Subgroup.Center

/-! A central element of the original positive group has no first-height
coefficient at any vertex with an adjacent neighbor. Literal degree
projection and all-characteristic adjacent-bracket nonvanishing prove this;
no full ordered-root factorization or highest-root centre is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCenterFirstLayer
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGGeckSerreRepresentation
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckHeightSupport CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckPositiveFirstLayer
open CFSGNormTwoCoordinateLeadingFactor CFSGNormTwoCoordinateLeadingHom
open CFSGNormTwoCoordinateDerivedFirstLayer CFSGNormTwoCoordinateHeight
open CFSGGradedMatrixGroupFirstLayer CFSGGradedMatrixSubgroups
open CFSGGradedMatrixCommutatorSecondLayer CFSGGradedMatrixDistinctDegreeCoordinates
open CFSGGradedMatrixSingleDegreeSpan CFSGNormTwoGeckSimpleBracketDegrees
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀
local notation "w" => weight A hs hp b₀ coordinateHeight
local notation "ell" => latticeWeight A hs hp b₀
local notation "U" => rootGroup A hs hp b₀ s₀ K false

theorem leading_coefficient_zero_of_commutes (u : U) (i j : Fin r)
    (hji : A j i= -1)
    (hcomm : u.val*canonicalRoot D K false i 1=canonicalRoot D K false i 1*u.val) :
    leadingCoordinates A hd hs hp ho K u.val j=0 := by
  have hu := (positive_firstLayer_mem_span A hs hp b₀ s₀ coordinateHeight
    (simple_height A hd hs hp ho) K u.val u.property).1
  have hi := simple_strict A hs hp b₀ s₀ coordinateHeight
    (simple_height A hd hs hp ho) K i 1
  have hc : u.val*canonicalRoot D K false i 1*u.val⁻¹*
      (canonicalRoot D K false i 1)⁻¹=1 := by rw [hcomm];group
  have hh := commutator_secondLayer w u.val (canonicalRoot D K false i 1) hu hi
  rw [hc,Units.val_one,sub_self,map_zero,
    simple_firstLayer A hs hp b₀ s₀ coordinateHeight (simple_height A hd hs hp ho),
    one_smul] at hh
  have hbracket : ⁅firstLayer w u.val,fieldRoot D K false i⁆=0 := hh.symm
  rw [positive_firstLayer_eq_coordinates A hd hs hp ho K u.val u.property] at hbracket
  have hsum : (∑k,leadingCoordinates A hd hs hp ho K u.val k •
      ⁅fieldRoot D K false k,fieldRoot D K false i⁆)=0 := by
    simpa only [sum_lie,smul_lie] using hbracket
  let d : Fin r→Fin r→ℤ := fun k=>(s₀ k:Roots A).val+(s₀ i:Roots A).val
  have hdinj : Function.Injective d := by
    intro k l h
    have hval : (s₀ k:Roots A).val=(s₀ l:Roots A).val := add_right_cancel h
    exact (s₀).injective (Subtype.ext (Subtype.ext hval))
  have hpj := congrArg (degreePart ell (d j)) hsum
  rw [degreePart_sum ell d hdinj
    (fun k=>⁅fieldRoot D K false k,fieldRoot D K false i⁆)
    (fun k=>simple_bracket_support A hs hp b₀ s₀ K k i)
    (leadingCoordinates A hd hs hp ho K u.val) j,map_zero] at hpj
  have hcartan : cartan b₀ s₀ j i= -1 := by
    change (b₀).cartanMatrix (s₀ i) (s₀ j)= -1
    rw [coordinate_cartan_transpose A hd hs hp ho]
    exact hji
  exact (smul_eq_zero.mp hpj).resolve_right
    (adjacent_bracket_ne_zero A hs hp b₀ s₀ K j i hcartan)

theorem center_firstLayer_zero (hneighbor : ∀j : Fin r,∃i,A j i= -1)
    (u : U) (hu : u∈Subgroup.center U) : firstLayer w u.val=0 := by
  have hc : leadingCoordinates A hd hs hp ho K u.val=0 := by
    funext j
    obtain ⟨i,hji⟩ := hneighbor j
    apply leading_coefficient_zero_of_commutes A hd hs hp ho K u i j hji
    have hh := congrArg Subtype.val ((Subgroup.mem_center_iff.mp hu)
      (positiveRoot A hd hs hp ho K i 1)).symm
    exact hh
  rw [positive_firstLayer_eq_coordinates A hd hs hp ho K u.val u.property,hc]
  simp only [Pi.zero_apply,zero_smul,Finset.sum_const_zero]

theorem center_le_derived (hneighbor : ∀j : Fin r,∃i,A j i= -1) :
    Subgroup.center U≤commutator U := by
  intro u hu
  exact (firstLayer_zero_iff_mem_derived A hd hs hp ho K u).mp
    (center_firstLayer_zero A hd hs hp ho K hneighbor u hu)

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCenterFirstLayer
