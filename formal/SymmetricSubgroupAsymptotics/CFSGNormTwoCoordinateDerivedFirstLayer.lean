import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLeadingHom
import SymmetricSubgroupAsymptotics.CFSGGeneratedAdditiveCoordinateKernel

/-! The zero-first-layer subgroup is the ACTUAL derived subgroup of U.
All root coordinates, their additive laws and generation are supplied by
the original coordinate model. No additional abelianization hypothesis
or higher-root factorization premise is retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDerivedFirstLayer
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckHeightSupport
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckPositiveFirstLayer
open CFSGNormTwoGeckOrderedSimpleFactor CFSGNormTwoCoordinateLeadingFactor
open CFSGNormTwoCoordinateLeadingHom CFSGGradedMatrixGroupFirstLayer
open CFSGGradedMatrixLieFirstLayer CFSGGradedMatrixOrderedFirstLayer CFSGNormTwoCoordinateHeight
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "w" => weight A hs hp b₀ coordinateHeight
local notation "U" => rootGroup A hs hp b₀ s₀ K false

theorem leading_kernel_eq_derived : (leadingHom A hd hs hp ho K).ker=commutator U :=
  CFSGGeneratedAdditiveCoordinateKernel.coordinate_kernel_eq_commutator
    (fun i a=>positiveRoot A hd hs hp ho K i a)
    (positiveRoot_zero A hd hs hp ho K) (positiveRoot_add A hd hs hp ho K)
    (leadingHom A hd hs hp ho K) (leadingHom_positiveRoot A hd hs hp ho K)
    (positiveRoot_generates A hd hs hp ho K)

theorem firstLayer_zero_iff_mem_derived (u : U) :
    firstLayer w u.val=0↔u∈commutator U := by
  rw [←leading_kernel_eq_derived A hd hs hp ho K,MonoidHom.mem_ker]
  change firstLayer w u.val=0↔leadingCoordinates A hd hs hp ho K u.val=0
  constructor
  · intro hz
    funext i
    have hh := congrArg (fun M : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K=>
      M (Sum.inl (s₀ i)) (Sum.inr (CFSGNormTwoGeckColumns.negativeIndex A hs hp (s₀ i)))) hz
    dsimp only at hh
    rw [firstLayer_entry] at hh
    exact hh
  · intro hc
    rw [positive_firstLayer_eq_coordinates A hd hs hp ho K u.val u.property,hc]
    simp only [Pi.zero_apply,zero_smul,Finset.sum_const_zero]

theorem height_two_iff_mem_derived (u : U) :
    (∀i j,w i≤w j+1→(u.val : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K) i j=
      (1 : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K) i j)↔u∈commutator U := by
  constructor
  · intro hhigh
    apply (firstLayer_zero_iff_mem_derived A hd hs hp ho K u).mp
    apply Matrix.ext
    intro i j
    rw [firstLayer,firstPart_apply]
    by_cases hij : w i=w j+1
    · rw [if_pos hij]
      change (u.val : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K) i j-
        (1 : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K) i j=0
      rw [hhigh i j (le_of_eq hij),sub_self]
    · rw [if_neg hij]
      rfl
  · intro hu
    apply height_two_of_firstLayer_zero w u.val
      (positive_firstLayer_mem_span A hs hp b₀ s₀ coordinateHeight
        (simple_height A hd hs hp ho) K u.val u.property).1
    exact (firstLayer_zero_iff_mem_derived A hd hs hp ho K u).mpr hu

theorem ordered_factor_with_derived_remainder (u : U) :
    ∃v : commutator U,u.val=v.val.val*
      orderedSimple A hs hp b₀ s₀ K (leadingCoordinates A hd hs hp ho K u.val) := by
  obtain ⟨v,hv,hhigh,hfac⟩ := ordered_leading_factor A hd hs hp ho K u.val u.property
  let vU : U := ⟨v,hv⟩
  have hvD : vU∈commutator U := (height_two_iff_mem_derived A hd hs hp ho K vU).mp hhigh
  exact ⟨⟨vU,hvD⟩,hfac⟩

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDerivedFirstLayer
