import SymmetricSubgroupAsymptotics.RepresentationPolynomialGeneratorBound
import SymmetricSubgroupAsymptotics.PermutationOrbitCoverGenerators

/-!
# Cyclic point-orbit covers in arbitrary characteristic

For one permutation, the delta functions at orbit representatives generate
its polynomial module. The PID theorem then uniformly bounds all invariant
subspaces. The acting element may have order divisible by the characteristic.
No finite group, invertible-order, or vector-census premise is needed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical Polynomial BigOperators

namespace SymmetricSubgroupAsymptotics

variable {k G X : Type} [Field k] [Group G]
  [Fintype X] [DecidableEq X] [MulAction G X]

/-- Orbit delta functions generate the polynomial module of an arbitrary
acting permutation, including in defining characteristic. -/
theorem permutationFunctionRepresentation_polynomial_span_orbitCover
    (g : G) {n : ℕ} (representative : Fin n → X)
    (hcover : ∀ x : X, ∃ (j : Fin n) (m : ℕ), g ^ m • representative j = x) :
    Submodule.span k[X]
      (Set.range (fun j ↦ Module.AEval'.of
        (permutationFunctionRepresentation k G X g)
        (Pi.single (representative j) (1 : k)))) = ⊤ := by
  let rho := permutationFunctionRepresentation k G X
  let polyEquiv := Module.AEval'.of (rho g)
  let code : Fin n → Module.AEval' (rho g) :=
    fun j ↦ polyEquiv (Pi.single (representative j) 1)
  let P : Submodule k[X] (Module.AEval' (rho g)) :=
    Submodule.span k[X] (Set.range code)
  have hdelta : ∀ x : X, polyEquiv (Pi.single x (1 : k)) ∈ P := by
    intro x
    obtain ⟨j, m, hm⟩ := hcover x
    have hcode : code j ∈ P := Submodule.subset_span ⟨j, rfl⟩
    have hpow := P.smul_mem ((Polynomial.X : k[X]) ^ m) hcode
    have heq : ((Polynomial.X : k[X]) ^ m) • code j =
        polyEquiv (rho (g ^ m) (Pi.single (representative j) 1)) := by
      dsimp only [code, polyEquiv]
      rw [Module.AEval'.X_pow_smul_of, map_pow]
      rfl
    rw [heq] at hpow
    simpa only [rho, permutationFunctionRepresentation_single, hm] using hpow
  have hall : ∀ v : X → k, polyEquiv v ∈ P := by
    intro v
    have hdecomp : (∑ i, v i • (Pi.single i 1 : X → k)) = v := by
      calc
        (∑ i, v i • (Pi.single i 1 : X → k)) = ∑ i, Pi.single i (v i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← Pi.single_smul]
          simp
        _ = v := LinearMap.sum_single_apply (fun _ : X ↦ k) v
    have hp : (∑ i, v i • polyEquiv (Pi.single i 1)) ∈ P :=
      P.sum_mem fun i _ ↦ P.smul_of_tower_mem (v i) (hdelta i)
    have heq : (∑ i, v i • polyEquiv (Pi.single i 1)) = polyEquiv v := by
      simpa only [map_sum, map_smul] using congrArg polyEquiv hdecomp
    exact heq ▸ hp
  apply top_unique
  intro x _
  simpa only [LinearEquiv.apply_symm_apply] using hall (polyEquiv.symm x)

/-- One `n`-place cyclic point-orbit cover gives a uniform `n`-generator
bound, with no restriction on the characteristic or the element order. -/
theorem permutationFunctionRepresentation_uniform_of_polynomial_orbitCover
    (g : G) {n : ℕ} (representative : Fin n → X)
    (hcover : ∀ x : X, ∃ (j : Fin n) (m : ℕ), g ^ m • representative j = x) :
    UniformSubrepresentationGeneratorBound (permutationFunctionRepresentation k G X) n :=
  uniformSubrepresentationGeneratorBound_of_polynomial _ g _
    (permutationFunctionRepresentation_polynomial_span_orbitCover g representative hcover)

end SymmetricSubgroupAsymptotics

end
