import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.Data.Fintype.EquivFin

/-! Two distinct scalar factors of an annihilating quadratic give actual
complementary eigenspaces and an actual eigenbasis over the original field.
This is a polynomial Bezout decomposition, valid in every characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteThreeDistinctEigenbasis

open Polynomial Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem eigenspaces_isCompl (A : Module.End K V) (a b : K) (hab : a ≠ b)
    (hz : (A - a • 1) * (A - b • 1) = 0) :
    IsCompl (A.eigenspace a) (A.eigenspace b) := by
  have hco : IsCoprime (X - C a) (X - C b) :=
    Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hab).isUnit
  have heval : aeval A ((X - C a) * (X - C b)) = 0 := by
    simpa only [map_mul, aeval_sub, aeval_X, aeval_C,
      Algebra.algebraMap_eq_smul_one] using hz
  refine ⟨?_, codisjoint_iff.mpr ?_⟩
  · simpa only [Module.End.eigenspace_def, aeval_sub, aeval_X, aeval_C,
      Algebra.algebraMap_eq_smul_one] using
      Polynomial.disjoint_ker_aeval_of_isCoprime A hco
  · have hh := Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime A hco
    rw [heval, LinearMap.ker_zero] at hh
    simpa only [Module.End.eigenspace_def, aeval_sub, aeval_X, aeval_C,
      Algebra.algebraMap_eq_smul_one] using hh

theorem exists_eigenbasis [Module.Finite K V] (A : Module.End K V)
    (hd : Module.finrank K V = 3) (a b : K) (hab : a ≠ b)
    (hz : (A - a • 1) * (A - b • 1) = 0) :
    ∃ c : Basis (Fin 3) K V, ∀ i,
      A (c i) = a • c i ∨ A (c i) = b • c i := by
  classical
  let P := A.eigenspace a
  let Q := A.eigenspace b
  have hc : IsCompl P Q := eigenspaces_isCompl A a b hab hz
  let p := Module.finBasis K P
  let q := Module.finBasis K Q
  let I := Fin (Module.finrank K P) ⊕ Fin (Module.finrank K Q)
  let B : Basis I K V := (p.prod q).map (Submodule.prodEquivOfIsCompl P Q hc)
  have hB : ∀ i : I, A (B i) = a • B i ∨ A (B i) = b • B i := by
    intro i
    cases i with
    | inl i =>
      left
      have hi : B (Sum.inl i) = (p i : V) := by
        have hp : (p.prod q) (Sum.inl i) = (p i, (0 : Q)) :=
          Prod.ext (Module.Basis.prod_apply_inl_fst p q i)
            (Module.Basis.prod_apply_inl_snd p q i)
        change (Submodule.prodEquivOfIsCompl P Q hc) ((p.prod q) (Sum.inl i)) = _
        rw [hp]
        exact add_zero _
      rw [hi]
      exact Module.End.mem_eigenspace_iff.mp (p i).property
    | inr i =>
      right
      have hi : B (Sum.inr i) = (q i : V) := by
        have hp : (p.prod q) (Sum.inr i) = ((0 : P), q i) :=
          Prod.ext (Module.Basis.prod_apply_inr_fst p q i)
            (Module.Basis.prod_apply_inr_snd p q i)
        change (Submodule.prodEquivOfIsCompl P Q hc) ((p.prod q) (Sum.inr i)) = _
        rw [hp]
        exact zero_add _
      rw [hi]
      exact Module.End.mem_eigenspace_iff.mp (q i).property
  have hI : Fintype.card I = 3 := by
    simp only [I, Fintype.card_sum, Fintype.card_fin]
    exact (Submodule.finrank_add_eq_of_isCompl hc).trans hd
  let e : I ≃ Fin 3 := Fintype.equivFinOfCardEq hI
  refine ⟨B.reindex e, fun i => ?_⟩
  simpa only [Module.Basis.reindex_apply] using hB (e.symm i)

end SymmetricSubgroupAsymptotics.FiniteThreeDistinctEigenbasis
