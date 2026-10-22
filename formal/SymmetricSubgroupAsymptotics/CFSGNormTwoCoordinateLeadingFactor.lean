import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrderedSimpleFactor
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSimpleRootCoordinates
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHeight
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCartan

/-! The first ordered positive-root layer for the ORIGINAL coordinate
model, with no supplied height chart or leading-term hypothesis. Its
parameters are literal matrix entries and are unique. Removing that
ordered simple factor leaves a height-at-least-two element of the SAME U. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLeadingFactor
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckHeightSupport CFSGNormTwoGeckColumns
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckPositiveFirstLayer
open CFSGNormTwoGeckOrderedSimpleFactor CFSGNormTwoGeckSimpleRootCoordinates
open CFSGGradedMatrixGroupFirstLayer CFSGGradedMatrixOrderedFirstLayer
open CFSGGradedMatrixLieFirstLayer CFSGGradedMatrixSubgroups CFSGNormTwoCoordinateHeight
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀
local notation "w" => weight A hs hp b₀ coordinateHeight

def leadingCoordinates (K : Type) [Field K]
    (u : (Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ) : Fin r→K :=
  fun i=>(u : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)
    (Sum.inl (s₀ i)) (Sum.inr (negativeIndex A hs hp (s₀ i)))

theorem firstLayer_entry (K : Type) [Field K]
    (u : (Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ) (i : Fin r) :
    firstLayer w u (Sum.inl (s₀ i)) (Sum.inr (negativeIndex A hs hp (s₀ i)))=
      leadingCoordinates A hd hs hp ho K u i := by
  have hwt : w (Sum.inl (s₀ i))=w (Sum.inr (negativeIndex A hs hp (s₀ i)))+1 := by
    change 0=coordinateHeight (negativeIndex A hs hp (s₀ i)).val+1
    rw [negative_val,map_neg,simple_height A hd hs hp ho]
    omega
  rw [firstLayer,firstPart_apply,if_pos hwt]
  change (u : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)
    (Sum.inl (s₀ i)) (Sum.inr (negativeIndex A hs hp (s₀ i)))-
      (1 : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)
        (Sum.inl (s₀ i)) (Sum.inr (negativeIndex A hs hp (s₀ i)))= _
  simp only [Matrix.one_apply,Sum.inl_ne_inr,if_false,sub_zero]
  rfl

theorem positive_firstLayer_eq_coordinates (K : Type) [Field K]
    (u : (Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ)
    (hu : u∈rootGroup A hs hp b₀ s₀ K false) :
    firstLayer w u=∑i,leadingCoordinates A hd hs hp ho K u i • fieldRoot D K false i := by
  obtain ⟨c,hc⟩ := exists_leading_coefficients A hs hp b₀ s₀ coordinateHeight
    (simple_height A hd hs hp ho) K u hu
  have hcoords : c=leadingCoordinates A hd hs hp ho K u := by
    funext i
    have hh := congrArg (fun M : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K=>
      M (Sum.inl (s₀ i)) (Sum.inr (negativeIndex A hs hp (s₀ i)))) hc
    dsimp only at hh
    rw [simple_sum_coordinate,firstLayer_entry] at hh
    exact hh
  simpa only [hcoords] using hc.symm

theorem ordered_leading_factor (K : Type) [Field K]
    (u : (Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ)
    (hu : u∈rootGroup A hs hp b₀ s₀ K false) :
    ∃v : (Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ,
      v∈rootGroup A hs hp b₀ s₀ K false ∧
      (∀i j,w i≤w j+1→(v : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K) i j=
        (1 : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K) i j) ∧
      u=v*orderedSimple A hs hp b₀ s₀ K (leadingCoordinates A hd hs hp ho K u) := by
  let q := orderedSimple A hs hp b₀ s₀ K (leadingCoordinates A hd hs hp ho K u)
  have hq : q∈rootGroup A hs hp b₀ s₀ K false := orderedSimple_mem_positive A hs hp b₀ s₀ K _
  have hu' := (positive_firstLayer_mem_span A hs hp b₀ s₀ coordinateHeight
    (simple_height A hd hs hp ho) K u hu).1
  have hq' := (positive_firstLayer_mem_span A hs hp b₀ s₀ coordinateHeight
    (simple_height A hd hs hp ho) K q hq).1
  refine ⟨u*q⁻¹,(rootGroup A hs hp b₀ s₀ K false).mul_mem hu
    ((rootGroup A hs hp b₀ s₀ K false).inv_mem hq),?_,?_⟩
  · apply height_two_of_firstLayer_zero w (u*q⁻¹)
      ((strictUnits w).mul_mem hu' ((strictUnits w).inv_mem hq'))
    apply matching_firstLayer_correction w u q hu' hq'
    rw [orderedSimple_firstLayer A hs hp b₀ s₀ coordinateHeight (simple_height A hd hs hp ho)]
    exact positive_firstLayer_eq_coordinates A hd hs hp ho K u hu
  · change u=(u*q⁻¹)*q
    simp only [mul_assoc,inv_mul_cancel,mul_one]

theorem leading_factor_unique (K : Type) [Field K]
    (u v : (Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K)ˣ)
    (hu : u∈rootGroup A hs hp b₀ s₀ K false) (hv : v∈rootGroup A hs hp b₀ s₀ K false)
    (hhigh : ∀i j,w i≤w j+1→(v : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K) i j=
      (1 : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K) i j)
    (c : Fin r→K) (hfac : u=v*orderedSimple A hs hp b₀ s₀ K c) :
    c=leadingCoordinates A hd hs hp ho K u := by
  have hzero : firstLayer w v=0 := by
    apply Matrix.ext
    intro i j
    rw [firstLayer,firstPart_apply]
    by_cases hij : w i=w j+1
    · rw [if_pos hij]
      change (v : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K) i j-
        (1 : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K) i j=0
      rw [hhigh i j (le_of_eq hij),sub_self]
    · rw [if_neg hij]
      rfl
  have hv' := (positive_firstLayer_mem_span A hs hp b₀ s₀ coordinateHeight
    (simple_height A hd hs hp ho) K v hv).1
  have hq' := (positive_firstLayer_mem_span A hs hp b₀ s₀ coordinateHeight
    (simple_height A hd hs hp ho) K _ (orderedSimple_mem_positive A hs hp b₀ s₀ K c)).1
  have hh := congrArg (firstLayer w) hfac
  rw [firstLayer_mul w _ _ hv' hq',hzero,zero_add,
    orderedSimple_firstLayer A hs hp b₀ s₀ coordinateHeight (simple_height A hd hs hp ho)] at hh
  apply simple_coefficients_unique A hs hp b₀ s₀ K
  exact hh.symm.trans (positive_firstLayer_eq_coordinates A hd hs hp ho K u hu)

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLeadingFactor
