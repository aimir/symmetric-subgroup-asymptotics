import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckPositiveFirstLayer
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixCommutatorSecondLayer
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixGroupSecondLayer

/-! Literal simple-root commutators realize every bracket coefficient
in height two. Their membership in the original positive group is proved;
there is no assumed height-two root chart or normalization. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSimpleCommutatorLayer
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckHeightSupport
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckPositiveFirstLayer
open CFSGGradedMatrixGroupFirstLayer CFSGGradedMatrixGroupSecondLayer
open CFSGGradedMatrixCommutatorSecondLayer
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

local notation "D" => realizationData A hs hp b s

def simpleCommutator (K : Type) [Field K] (i j : Fin r) (a : K) :
    (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ :=
  canonicalRoot D K false i 1*canonicalRoot D K false j a*
    (canonicalRoot D K false i 1)⁻¹*(canonicalRoot D K false j a)⁻¹

theorem simpleCommutator_mem_positive (K : Type) [Field K] (i j : Fin r) (a : K) :
    simpleCommutator A hs hp b s K i j a∈rootGroup A hs hp b s K false := by
  have hi : canonicalRoot D K false i 1∈rootGroup A hs hp b s K false :=
    Subgroup.subset_closure ⟨(i,1),rfl⟩
  have hj : canonicalRoot D K false j a∈rootGroup A hs hp b s K false :=
    Subgroup.subset_closure ⟨(j,a),rfl⟩
  exact (rootGroup A hs hp b s K false).mul_mem
    ((rootGroup A hs hp b s K false).mul_mem
      ((rootGroup A hs hp b s K false).mul_mem hi hj)
      ((rootGroup A hs hp b s K false).inv_mem hi))
    ((rootGroup A hs hp b s K false).inv_mem hj)

variable (height : (n→ℤ)→ₗ[ℤ]ℤ) (hheight : ∀i : b.support,height (i:Roots A).val=1)
include hheight
local notation "w" => weight A hs hp b height

theorem simpleCommutator_firstLayer (K : Type) [Field K] (i j : Fin r) (a : K) :
    firstLayer w (simpleCommutator A hs hp b s K i j a)=0 :=
  commutator_firstLayer_zero w _ _
    (simple_strict A hs hp b s height hheight K i 1)
    (simple_strict A hs hp b s height hheight K j a)

theorem simpleCommutator_secondLayer (K : Type) [Field K] (i j : Fin r) (a : K) :
    secondLayer w (simpleCommutator A hs hp b s K i j a)=
      a • ⁅fieldRoot D K false i,fieldRoot D K false j⁆ := by
  change CFSGGradedMatrixSingleDegreeSpan.degreePart w (2:ℤ)
    (((canonicalRoot D K false i 1*canonicalRoot D K false j a*
      (canonicalRoot D K false i 1)⁻¹*(canonicalRoot D K false j a)⁻¹ :
        (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ) :
          Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)-1)=_
  rw [commutator_secondLayer w _ _
    (simple_strict A hs hp b s height hheight K i 1)
    (simple_strict A hs hp b s height hheight K j a),
    simple_firstLayer A hs hp b s height hheight,
    simple_firstLayer A hs hp b s height hheight,one_smul,lie_smul]

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSimpleCommutatorLayer
