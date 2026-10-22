import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDerivedFirstLayer
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixDerivedSecondLayer

/-! Every element of the SAME actual positive derived subgroup has its
height-two coefficient in the bracket span of the original simple-root
operators. All first-layer and subgroup hypotheses are discharged by the
coordinate construction. Higher ordered-root collection is not assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDerivedSecondLayer
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckHeightSupport
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckPositiveFirstLayer
open CFSGNormTwoCoordinateHeight CFSGGradedMatrixGroupSecondLayer
open CFSGGradedMatrixDerivedSecondLayer
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

theorem derived_secondLayer_mem (u : U) (hu : u∈commutator U) :
    secondLayer w u.val∈bracketSpan (fun i : Fin r=>fieldRoot D K false i) := by
  exact (derived_secondLayer_mem_bracketSpan w U
    (fun i : Fin r=>fieldRoot D K false i)
    (fun v=>(positive_firstLayer_mem_span A hs hp b₀ s₀ coordinateHeight
      (simple_height A hd hs hp ho) K v.val v.property).1)
    (fun v=>(positive_firstLayer_mem_span A hs hp b₀ s₀ coordinateHeight
      (simple_height A hd hs hp ho) K v.val v.property).2) u hu).2

theorem height_two_secondLayer_mem (u : U)
    (hhigh : ∀i j,w i≤w j+1→
      (u.val : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K) i j=
        (1 : Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K) i j) :
    secondLayer w u.val∈bracketSpan (fun i : Fin r=>fieldRoot D K false i) := by
  exact derived_secondLayer_mem A hd hs hp ho K u
    ((CFSGNormTwoCoordinateDerivedFirstLayer.height_two_iff_mem_derived
      A hd hs hp ho K u).mp hhigh)

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDerivedSecondLayer
