import SymmetricSubgroupAsymptotics.CFSGInvariantQuotientAction
import SymmetricSubgroupAsymptotics.CFSGSerreRootOperatorInvertible

/-! Divided-power-stable kernels are preserved in both directions by every
original root element. Inverse stability is proved from local unipotence;
it is not inferred merely from forward invariance of a linear subspace. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSerreInvariantKernel
open CFSGInvariantQuotientAction CFSGSerreLocalNilpotence CFSG.Models.Chevalley

section General
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem restrict_pow_val (D : Module.End R M) (S : Submodule R M)
    (hS : ∀ x ∈ S, D x ∈ S) (n : ℕ) (x : S) :
    (((D.restrict hS) ^ n) x).val = (D ^ n) x.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply]
    exact congrArg D ih

theorem inverse_mem_of_locally_unipotent (D : Module.End R M)
    (hD : ∀ x : M, ∃ n : ℕ, (D ^ n) x = 0) (S : Submodule R M)
    (hS : ∀ x ∈ S, D x ∈ S) (e : M ≃ₗ[R] M) (he : e.toLinearMap = 1 + D)
    (x : M) (hx : x ∈ S) : e.symm x ∈ S := by
  have hloc : ∀ y : S, ∃ n : ℕ, ((D.restrict hS) ^ n) y = 0 := by
    intro y
    obtain ⟨n, hn⟩ := hD y.val
    refine ⟨n, Subtype.ext ?_⟩
    rw [restrict_pow_val, hn]
    rfl
  obtain ⟨y, hy⟩ := (one_add_bijective_of_locally_nilpotent (D.restrict hS) hloc).2
    (⟨x, hx⟩ : S)
  have hyv := congrArg Subtype.val hy
  change y.val + D y.val = x at hyv
  have hey : e y.val = x := by
    have h := congrArg (fun f : Module.End R M => f y.val) he
    change e y.val = y.val + D y.val at h
    exact h.trans hyv
  have hxy : e.symm x = y.val := by
    apply e.injective
    rw [LinearEquiv.apply_symm_apply, hey]
  rw [hxy]
  exact y.property

theorem mem_stabilizer_of_locally_unipotent (D : Module.End R M)
    (hD : ∀ x : M, ∃ n : ℕ, (D ^ n) x = 0) (S : Submodule R M)
    (hS : ∀ x ∈ S, D x ∈ S) (e : M ≃ₗ[R] M) (he : e.toLinearMap = 1 + D) :
    e ∈ stabilizer S := by
  constructor
  · intro x hx
    change e.toLinearMap x ∈ S
    rw [he]
    exact S.add_mem hx (hS x hx)
  · exact inverse_mem_of_locally_unipotent D hD S hS e he
end General

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (K : Type) [Field K]
    (S : Submodule K (Space A K))
    (hS : ∀ negative i k x, x ∈ S →
      (integralOperator A negative i k).baseChange K x ∈ S)
include hS

theorem positiveRootPart_mem (negative : Bool) (i : Fin n) (t : K)
    (x : Space A K) (hx : x ∈ S) : positiveRootPart A K negative i t x ∈ S := by
  simp only [positiveRootPart, LinearMap.sum_apply, LinearMap.smul_apply]
  apply S.sum_mem
  intro j _
  exact S.smul_mem _ (hS negative i (j + 1) x hx)

theorem rootElement_mem_stabilizer (negative : Bool) (i : Fin n) (t : K)
    (g : Ambient A K) (hg : IsRootElement A K negative i t g) : g ∈ stabilizer S :=
  mem_stabilizer_of_locally_unipotent (positiveRootPart A K negative i t)
    (positiveRootPart_locally_nilpotent A K negative i t) S
    (positiveRootPart_mem A K S hS negative i t) g
    (hg.trans (rootOperator_eq_one_add_positiveRootPart A K negative i t))

theorem model_le_stabilizer : subgroup A K ≤ stabilizer S := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨negative, i, t, hg⟩
  exact rootElement_mem_stabilizer A K S hS negative i t g hg

end SymmetricSubgroupAsymptotics.CFSGSerreInvariantKernel
