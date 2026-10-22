import SymmetricSubgroupAsymptotics.CFSGGradedMatrixGroupFirstLayer
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckPositivePGroup
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFunctionalSupport

/-! Unconditional leading-term recognition for actual positive Geck
GROUP words. The first height layer lies in the original simple E_i span
in every characteristic; this is not assumed from matrix homogeneity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckPositiveFirstLayer
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckHeightSupport
open CFSGNormTwoGeckFunctionalSupport CFSGNormTwoGeckPositivePGroup
open CFSGGradedMatrixLieFirstLayer CFSGGradedMatrixGroupFirstLayer
open CFSGGradedMatrixSubgroups
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)
    (height : (n→ℤ)→ₗ[ℤ]ℤ) (hheight : ∀i : b.support,height (i:Roots A).val=1)

local notation "D" => realizationData A hs hp b s
local notation "w" => weight A hs hp b height

include hheight

theorem simple_firstPart (K : Type) [Field K] (i : Fin r) :
    firstPart w (fieldRoot D K false i)=fieldRoot D K false i := by
  apply firstPart_eq_of_supported
  intro j k hjk
  apply field_E_degree A hs hp b s height K i j k
  simpa only [hheight] using hjk

theorem second_firstPart_zero (K : Type) [Field K] (i : Fin r) :
    firstPart w (fieldSecond D K false i)=0 := by
  apply Matrix.ext
  intro j k
  rw [firstPart_apply]
  by_cases hjk : w j=w k+1
  · rw [if_pos hjk]
    apply field_second_degree A hs hp b s height K i j k
    rw [hheight]
    omega
  · rw [if_neg hjk]
    rfl

theorem simple_firstLayer (K : Type) [Field K] (i : Fin r) (a : K) :
    firstLayer w (canonicalRoot D K false i a)=a • fieldRoot D K false i := by
  change firstPart w ((canonicalRoot D K false i a : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)-1)=_
  rw [canonicalRoot_val]
  have he : (1+a • fieldRoot D K false i+a^2 • fieldSecond D K false i)-1=
      a • fieldRoot D K false i+a^2 • fieldSecond D K false i := by abel
  rw [he,map_add,map_smul,map_smul,simple_firstPart A hs hp b s height hheight,
    second_firstPart_zero A hs hp b s height hheight,smul_zero,add_zero]

theorem simple_strict (K : Type) [Field K] (i : Fin r) (a : K) :
    canonicalRoot D K false i a∈strictUnits w :=
  CFSGWeightedRootPGroup.quadratic_identity_on_nonincreasing w
    (canonicalRoot D K false i a) (fieldRoot D K false i) (fieldSecond D K false i) a
    (canonicalRoot_val D K false i a)
    (field_E_strict A hs hp b s height hheight K i)
    (field_second_strict A hs hp b s height hheight K i)

theorem positive_firstLayer_mem_span (K : Type) [Field K]
    (u : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ)
    (hu : u∈rootGroup A hs hp b s K false) :
    u∈strictUnits w ∧ firstLayer w u∈Submodule.span K
      (Set.range (fun i : Fin r=>fieldRoot D K false i)) := by
  apply generated_firstLayer_mem_span w
    (fun z : Fin r×K=>canonicalRoot D K false z.1 z.2)
    (Set.range (fun i : Fin r=>fieldRoot D K false i)) _ _ u hu
  · intro z
    exact simple_strict A hs hp b s height hheight K z.1 z.2
  · intro z
    rw [simple_firstLayer A hs hp b s height hheight]
    exact Submodule.smul_mem _ z.2 (Submodule.subset_span ⟨z.1,rfl⟩)

theorem exists_leading_coefficients (K : Type) [Field K]
    (u : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ)
    (hu : u∈rootGroup A hs hp b s K false) :
    ∃c : Fin r→K,∑i,c i • fieldRoot D K false i=firstLayer w u := by
  exact (Submodule.mem_span_range_iff_exists_fun K).mp
    (positive_firstLayer_mem_span A hs hp b s height hheight K u hu).2

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckPositiveFirstLayer
