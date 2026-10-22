import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckComplementGrading
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHeight
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCartan

/-! The excluded-simple grading is an explicit integer functional for
the actual coordinate base. Thus the complement-detection lemmas need
no extra grading-existence premise in the original E lattice models. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateExcludedHeight
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCoordinateHeight CFSGNormTwoGeckHeightSupport
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoGeckPositiveComplement CFSGNormTwoGeckComplementGrading
open CFSGSerreQuadraticMatrix CFSGGradedMatrixSubgroups
variable {r : ℕ}

def excludedHeight (i : Fin r) : (Fin r→ℤ)→ₗ[ℤ]ℤ :=
  coordinateHeight-LinearMap.proj i

theorem excludedHeight_single (i j : Fin r) :
    excludedHeight i (Pi.single j 1)=if i=j then 0 else 1 := by
  by_cases hij : i=j
  · simp [excludedHeight,coordinateHeight,CFSGIntegerHeightSign.height,Pi.single_apply,hij]
  · simp [excludedHeight,coordinateHeight,CFSGIntegerHeightSign.height,Pi.single_apply,hij,Ne.symm hij]

variable (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]

theorem excluded_simple_zero (i : Fin r) :
    excludedHeight i
      (coordinateIndexEquiv A hd hs hp ho i:Roots A).val=0 := by
  change excludedHeight i (Pi.single i 1)=0
  simpa only [if_pos rfl] using excludedHeight_single i i

theorem excluded_other_positive (i j : Fin r) (hij : i≠j) :
    0<excludedHeight i
      (coordinateIndexEquiv A hd hs hp ho j:Roots A).val := by
  change 0<excludedHeight i (Pi.single j 1)
  rw [excludedHeight_single,if_neg hij]
  exact zero_lt_one

theorem coordinate_positive_mem_complement_of_strict (i : Fin r)
    (K : Type) [Field K]
    (g : (Matrix ((coordinateBase A hd hs hp ho).support⊕Roots A)
      ((coordinateBase A hd hs hp ho).support⊕Roots A) K)ˣ)
    (hg : g∈rootGroup A hs hp (coordinateBase A hd hs hp ho)
      (coordinateIndexEquiv A hd hs hp ho) K false)
    (hstrict : g∈strictUnits
      (weight A hs hp (coordinateBase A hd hs hp ho) (excludedHeight i))) :
    g∈positiveComplement A hs hp (coordinateBase A hd hs hp ho)
      (coordinateIndexEquiv A hd hs hp ho) K i := by
  exact positive_mem_complement_of_strict A hs hp _ _ (excludedHeight i) i
    (excluded_simple_zero A hd hs hp ho i)
    (fun j hij=>excluded_other_positive A hd hs hp ho i j hij) K g hg hstrict

theorem coordinate_positive_mem_simple_of_preserves (i : Fin r)
    (K : Type) [Field K]
    (g : (Matrix ((coordinateBase A hd hs hp ho).support⊕Roots A)
      ((coordinateBase A hd hs hp ho).support⊕Roots A) K)ˣ)
    (hg : g∈rootGroup A hs hp (coordinateBase A hd hs hp ho)
      (coordinateIndexEquiv A hd hs hp ho) K false)
    (hpreserves : g∈preservingUnits
      (weight A hs hp (coordinateBase A hd hs hp ho) (excludedHeight i))) :
    g∈canonicalRootSubgroup
      (realizationData A hs hp (coordinateBase A hd hs hp ho)
        (coordinateIndexEquiv A hd hs hp ho)) K false i := by
  exact positive_mem_simple_of_preserves A hs hp _ _ (excludedHeight i) i
    (excluded_simple_zero A hd hs hp ho i)
    (fun j hij=>excluded_other_positive A hd hs hp ho i j hij) K g hg hpreserves

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateExcludedHeight
