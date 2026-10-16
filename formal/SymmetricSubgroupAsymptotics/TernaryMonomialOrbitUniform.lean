import SymmetricSubgroupAsymptotics.TernaryMonomialCocycle
import SymmetricSubgroupAsymptotics.RepresentationPolynomialGeneratorBound
import Mathlib.LinearAlgebra.Pi

/-! A cyclic point orbit gives a uniform generator bound for a ternary
monomial action, including sign-carrying lifts and defining characteristic.
Every orbit vector is a nonzero scalar multiple of a coordinate vector;
the polynomial PID bound then controls every invariant subspace. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical Polynomial BigOperators

namespace SymmetricSubgroupAsymptotics.TernaryMonomialOrbitUniform

variable {R X : Type} [Group R] [Fintype X] [DecidableEq X]
  (b : R →* Equiv.Perm X) (d : R → X → ZMod 3)
  (hone : ∀ i, d 1 i = 1)
  (hmul : ∀ g h i, d (g*h) i = d g i * d h (b g⁻¹ i))

abbrev representation : Representation (ZMod 3) R (X → ZMod 3) :=
  LinearSemidirectCoprimeSocleBounds.linearRepresentation
    (TernaryMonomialCocycle.linearAction b d hone hmul)

include hone hmul in
omit [Fintype X] [DecidableEq X] in
theorem coefficient_ne_zero (g : R) (i : X) : d g i ≠ 0 := by
  intro hz
  have h := TernaryMonomialCocycle.inverse_right b d hone hmul g i
  rw [hz,zero_mul] at h
  exact zero_ne_one h

theorem single (g : R) (i : X) (a : ZMod 3) :
    representation b d hone hmul g (Pi.single i a) =
      Pi.single (b g i) (d g (b g i)*a) := by
  funext j
  change d g j * (Pi.single i a : X → ZMod 3) (b g⁻¹ j) =
    (Pi.single (b g i) (d g (b g i)*a) : X → ZMod 3) j
  by_cases hj : j = b g i
  · subst j
    have he : b g⁻¹ (b g i) = i := by
      rw [map_inv]
      exact (b g).symm_apply_apply i
    rw [he,Pi.single_eq_same,Pi.single_eq_same]
  · have hn : b g⁻¹ j ≠ i := by
      intro hi
      apply hj
      rw [map_inv] at hi
      exact ((b g).eq_symm_apply.mp hi.symm).symm
    simp only [Pi.single_eq_of_ne hj,Pi.single_eq_of_ne hn,mul_zero]

theorem polynomial_span {n : ℕ} (g : R) (representative : Fin n → X)
    (hcover : ∀ x : X, ∃ (j : Fin n) (m : ℕ), ((b g)^m) (representative j) = x) :
    Submodule.span (ZMod 3)[X]
      (Set.range (fun j => Module.AEval'.of (representation b d hone hmul g)
        (Pi.single (representative j) (1 : ZMod 3)))) = ⊤ := by
  let rho : Representation (ZMod 3) R (X → ZMod 3) := representation b d hone hmul
  let e := Module.AEval'.of (rho g)
  let code : Fin n → Module.AEval' (rho g) := fun j => e (Pi.single (representative j) 1)
  let P : Submodule (ZMod 3)[X] (Module.AEval' (rho g)) :=
    Submodule.span (ZMod 3)[X] (Set.range code)
  have hdelta (x : X) : e (Pi.single x (1 : ZMod 3)) ∈ P := by
    obtain ⟨j,m,hm⟩ := hcover x
    have hcode : code j ∈ P := Submodule.subset_span ⟨j,rfl⟩
    have hpow := P.smul_mem ((Polynomial.X : (ZMod 3)[X])^m) hcode
    have heq : ((Polynomial.X : (ZMod 3)[X])^m) • code j =
        e (rho (g^m) (Pi.single (representative j) 1)) := by
      dsimp only [code,e]
      rw [Module.AEval'.X_pow_smul_of,map_pow]
      rfl
    rw [heq] at hpow
    have hpoint : b (g^m) (representative j) = x := by rw [map_pow]; exact hm
    change e (representation b d hone hmul (g^m) (Pi.single (representative j) 1)) ∈ P at hpow
    rw [single,hpoint,mul_one] at hpow
    have hnorm := P.smul_of_tower_mem ((d (g^m) x)⁻¹) hpow
    have hnormalize : (d (g^m) x)⁻¹ • e (Pi.single x (d (g^m) x)) =
        e (Pi.single x 1) := by
      rw [← map_smul,← Pi.single_smul,smul_eq_mul,
        inv_mul_cancel₀ (coefficient_ne_zero b d hone hmul (g^m) x)]
    exact hnormalize ▸ hnorm
  have hall (v : X → ZMod 3) : e v ∈ P := by
    have he : (∑ i, v i • (Pi.single i 1 : X → ZMod 3)) = v := by
      calc
        _ = ∑ i, Pi.single i (v i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← Pi.single_smul]
          simp
        _ = v := LinearMap.sum_single_apply (fun _ : X => ZMod 3) v
    have hp : (∑ i, v i • e (Pi.single i 1)) ∈ P :=
      P.sum_mem fun i _ => P.smul_of_tower_mem (v i) (hdelta i)
    have he' : (∑ i, v i • e (Pi.single i 1)) = e v := by
      simpa only [map_sum,map_smul] using congrArg e he
    exact he' ▸ hp
  apply top_unique
  intro x _
  simpa only [LinearEquiv.apply_symm_apply] using hall (e.symm x)

theorem uniform {n : ℕ} (g : R) (representative : Fin n → X)
    (hcover : ∀ x : X, ∃ (j : Fin n) (m : ℕ), ((b g)^m) (representative j) = x) :
    UniformSubrepresentationGeneratorBound (representation b d hone hmul) n :=
  uniformSubrepresentationGeneratorBound_of_polynomial _ g _
    (polynomial_span b d hone hmul g representative hcover)

end SymmetricSubgroupAsymptotics.TernaryMonomialOrbitUniform

end
