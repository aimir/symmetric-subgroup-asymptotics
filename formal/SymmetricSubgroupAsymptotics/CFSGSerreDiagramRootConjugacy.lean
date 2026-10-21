import SymmetricSubgroupAsymptotics.CFSGSerreDiagramLattice
import SymmetricSubgroupAsymptotics.CFSGSerreRootOperatorInvertible

/-! Base change of the actual integral diagram action intertwines the
original finite root-operator polynomials and their actual invertible lifts.
No exponential-additivity or uniform nilpotence premise is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical TensorProduct BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSerreDiagram
open CFSG.Models.Chevalley CFSGSerreLocalNilpotence
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (K : Type) [Field K]
    (p : Equiv.Perm (Fin n)) (hA : ∀ i j, A (p i) (p j) = A i j)
include hA

def spaceEquiv : Space A K ≃ₗ[K] Space A K :=
  (integralEquiv A p hA).baseChange ℤ K (integralLattice A) (integralLattice A)

theorem spaceEquiv_integralOperator (negative : Bool) (i : Fin n) (k : ℕ) (x : Space A K) :
    spaceEquiv A K p hA ((integralOperator A negative i k).baseChange K x) =
      (integralOperator A negative (p i) k).baseChange K (spaceEquiv A K p hA x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x =>
    simp only [spaceEquiv, LinearMap.baseChange_tmul, LinearEquiv.baseChange_tmul,
      integralEquiv_integralOperator]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem spaceEquiv_rootOperator (negative : Bool) (i : Fin n) (t : K) (x : Space A K) :
    spaceEquiv A K p hA (rootOperator A K negative i t x) =
      rootOperator A K negative (p i) t (spaceEquiv A K p hA x) := by
  simp only [rootOperator, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro k _
  rw [spaceEquiv_integralOperator]

theorem spaceEquiv_symm_rootOperator (negative : Bool) (j : Fin n) (t : K) (x : Space A K) :
    (spaceEquiv A K p hA).symm (rootOperator A K negative j t x) =
      rootOperator A K negative (p.symm j) t ((spaceEquiv A K p hA).symm x) := by
  apply (spaceEquiv A K p hA).injective
  rw [LinearEquiv.apply_symm_apply, spaceEquiv_rootOperator,
    Equiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem conjugate_rootOperator (negative : Bool) (i : Fin n) (t : K) :
    (spaceEquiv A K p hA).toLinearMap * rootOperator A K negative i t *
      (spaceEquiv A K p hA).symm.toLinearMap = rootOperator A K negative (p i) t := by
  apply LinearMap.ext
  intro x
  change spaceEquiv A K p hA (rootOperator A K negative i t ((spaceEquiv A K p hA).symm x)) = _
  rw [spaceEquiv_rootOperator, LinearEquiv.apply_symm_apply]

theorem conjugate_inverse_rootOperator (negative : Bool) (j : Fin n) (t : K) :
    (spaceEquiv A K p hA).symm.toLinearMap * rootOperator A K negative j t *
      (spaceEquiv A K p hA).toLinearMap = rootOperator A K negative (p.symm j) t := by
  apply LinearMap.ext
  intro x
  change (spaceEquiv A K p hA).symm (rootOperator A K negative j t (spaceEquiv A K p hA x)) = _
  rw [spaceEquiv_symm_rootOperator, LinearEquiv.symm_apply_apply]

theorem conjugate_isRootElement (negative : Bool) (i : Fin n) (t : K)
    (g : Ambient A K) (hg : IsRootElement A K negative i t g) :
    IsRootElement A K negative (p i) t ((MulAut.conj (spaceEquiv A K p hA)) g) := by
  change (spaceEquiv A K p hA).toLinearMap * g.toLinearMap *
    (spaceEquiv A K p hA).symm.toLinearMap = rootOperator A K negative (p i) t
  rw [hg]
  exact conjugate_rootOperator A K p hA negative i t

theorem conjugate_inverse_isRootElement (negative : Bool) (j : Fin n) (t : K)
    (g : Ambient A K) (hg : IsRootElement A K negative j t g) :
    IsRootElement A K negative (p.symm j) t ((MulAut.conj ((spaceEquiv A K p hA)⁻¹)) g) := by
  change (spaceEquiv A K p hA).symm.toLinearMap * g.toLinearMap *
    (spaceEquiv A K p hA).toLinearMap = rootOperator A K negative (p.symm j) t
  rw [hg]
  exact conjugate_inverse_rootOperator A K p hA negative j t

theorem conjugate_rootEquiv (negative : Bool) (i : Fin n) (t : K) :
    (MulAut.conj (spaceEquiv A K p hA)) (rootEquiv A K negative i t) =
      rootEquiv A K negative (p i) t := by
  apply LinearEquiv.toLinearMap_injective
  exact conjugate_isRootElement A K p hA negative i t _ rfl

end SymmetricSubgroupAsymptotics.CFSGSerreDiagram
