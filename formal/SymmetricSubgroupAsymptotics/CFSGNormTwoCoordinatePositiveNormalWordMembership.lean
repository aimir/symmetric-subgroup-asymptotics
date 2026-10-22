import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateFinitePositiveNormalForm
import Mathlib.Algebra.Group.Subgroup.Finite

/-! Actual ordered normal words remain in a subgroup containing their
actual root-parameter factors. This elementary product statement will
count centralizing-root words without assuming a root census. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveNormalWordMembership
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCoordinateRootHeightQuotient CFSGNormTwoCoordinateExactHeightLayer
open CFSGNormTwoCoordinateHeightLayerFactorization CFSGFiniteQuotientFamilyProduct
open CFSGNormTwoCoordinatePositiveRootGenerators CFSGNormTwoCoordinatePositiveHeightNormalForm
open CFSGNormTwoCoordinateRootParameterEquiv CFSGNormTwoCoordinateFinitePositiveNormalForm
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

theorem exactHeightWord_mem_of_parameters (K : Type) [Field K]
    (H : Subgroup (PositiveGroup A hd hs hp ho K)) (h : ℤ) (c : ExactHeightRoot A h→K)
    (hc : ∀k : ExactHeightRoot A h,
      positiveRootParameterHom A hd hs hp ho K k.val.val k.val.property (Multiplicative.ofAdd (c k))∈H) :
    exactHeightWord A hd hs hp ho K h c∈H := by
  classical
  rw [exactHeightWord,orderedFamilyProduct]
  apply H.list_prod_mem
  intro x hx
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp hx
  exact hc k

theorem positiveRootNormalWord_mem_of_parameters (K : Type) [Field K]
    (H : Subgroup (PositiveGroup A hd hs hp ho K)) (c : PositiveRoot A→K)
    (hc : ∀k : PositiveRoot A,
      positiveRootParameterHom A hd hs hp ho K k.val k.property (Multiplicative.ofAdd (c k))∈H) :
    positiveRootNormalWord A hd hs hp ho K c∈H := by
  classical
  rw [positiveRootNormalWord,positiveHeightNormalWord]
  apply H.list_prod_mem
  intro x hx
  obtain ⟨n,_,rfl⟩ := List.mem_map.mp hx
  apply exactHeightWord_mem_of_parameters A hd hs hp ho K H
  intro k
  rw [rootParameterEquiv_apply]
  exact hc k.val

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveNormalWordMembership
