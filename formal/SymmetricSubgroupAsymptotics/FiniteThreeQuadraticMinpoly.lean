import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Algebra.Polynomial.FieldDivision
import Lean.Elab.Tactic.Omega

/-! A quadratic minimal polynomial on an actual three-dimensional space
splits over the original field. Its linear characteristic-polynomial
cofactor supplies an eigenvalue, hence a root of the minimal polynomial.
No algebraic closure or finite-field counting is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteThreeQuadraticMinpoly

open Polynomial Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V]

theorem exists_root (A : Module.End K V) (hd : Module.finrank K V = 3)
    (hmin : (minpoly K A).natDegree = 2) :
    ∃ a : K, (minpoly K A).IsRoot a := by
  obtain ⟨q, hq⟩ := LinearMap.minpoly_dvd_charpoly A
  have hm0 : minpoly K A ≠ 0 := minpoly.ne_zero (LinearMap.isIntegral A)
  have hc0 : A.charpoly ≠ 0 := (LinearMap.charpoly_monic A).ne_zero
  have hq0 : q ≠ 0 := by
    intro h
    apply hc0
    rw [hq, h, mul_zero]
  have hqd : q.natDegree = 1 := by
    have he := Polynomial.natDegree_mul hm0 hq0
    rw [← hq, LinearMap.charpoly_natDegree, hd, hmin] at he
    omega
  obtain ⟨a, ha⟩ := Polynomial.exists_root_of_degree_eq_one
    ((Polynomial.degree_eq_iff_natDegree_eq_of_pos (by omega : 0 < (1 : ℕ))).mpr hqd)
  have hchar : A.charpoly.IsRoot a := by
    rw [hq]
    exact ha.dvd (dvd_mul_left q (minpoly K A))
  exact ⟨a, Module.End.isRoot_of_hasEigenvalue
    ((Module.End.hasEigenvalue_iff_isRoot_charpoly A a).mpr hchar)⟩

theorem exists_factorization (A : Module.End K V) (hd : Module.finrank K V = 3)
    (hmin : (minpoly K A).natDegree = 2) :
    ∃ a b : K, minpoly K A = (X - C a) * (X - C b) := by
  obtain ⟨a, ha⟩ := exists_root A hd hmin
  obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr ha
  have hm : (minpoly K A).Monic := minpoly.monic (LinearMap.isIntegral A)
  have hqm : q.Monic := (monic_X_sub_C a).of_mul_monic_left (hq ▸ hm)
  have hqd : q.natDegree = 1 := by
    have he := Polynomial.natDegree_mul (X_sub_C_ne_zero a) hqm.ne_zero
    rw [← hq, hmin, natDegree_X_sub_C] at he
    omega
  refine ⟨a, -q.coeff 0, ?_⟩
  have heq : q = X - C (-q.coeff 0) := by
    simpa only [C_neg, sub_neg_eq_add] using hqm.eq_X_add_C hqd
  exact hq.trans (congrArg (fun r : K[X] => (X - C a) * r) heq)

theorem exists_annihilating_pair (A : Module.End K V) (hd : Module.finrank K V = 3)
    (hmin : (minpoly K A).natDegree = 2) :
    ∃ a b : K, (A - a • 1) * (A - b • 1) = 0 := by
  obtain ⟨a, b, hab⟩ := exists_factorization A hd hmin
  refine ⟨a, b, ?_⟩
  have hz := minpoly.aeval K A
  rw [hab] at hz
  simpa only [map_mul, aeval_sub, aeval_X, aeval_C,
    Algebra.algebraMap_eq_smul_one] using hz

theorem scalar_or_annihilating_pair (A : Module.End K V)
    (hd : Module.finrank K V = 3) (hmin : (minpoly K A).natDegree ≤ 2) :
    (∃ a : K, A = a • 1) ∨ ∃ a b : K, (A - a • 1) * (A - b • 1) = 0 := by
  letI : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hd
  have hp := minpoly.natDegree_pos (LinearMap.isIntegral A)
  have he : (minpoly K A).natDegree = 1 ∨ (minpoly K A).natDegree = 2 := by omega
  rcases he with he | he
  · left
    obtain ⟨a, ha⟩ := minpoly.natDegree_eq_one_iff.mp he
    exact ⟨a, by simpa only [Algebra.algebraMap_eq_smul_one] using ha.symm⟩
  · exact Or.inr (exists_annihilating_pair A hd he)

end SymmetricSubgroupAsymptotics.FiniteThreeQuadraticMinpoly
