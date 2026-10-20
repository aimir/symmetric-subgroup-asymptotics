import SymmetricSubgroupAsymptotics.TernaryMonomialOrbitUniform

/-! Coordinate-dependent ternary signs preserve delta generators.
Transitivity of the actual signed monomial complement makes the full
four-coordinate module cyclic; no uniform scalar character is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical MonoidAlgebra BigOperators
namespace SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralTernaryOrbitGenerators
variable {H X : Type} [Group H] [Fintype X] [DecidableEq X]
  (b : H →* Equiv.Perm X) (d : H → X → ZMod 3)
  (hone : ∀ i, d 1 i=1)
  (hmul : ∀ g h i, d (g*h) i=d g i*d h (b g⁻¹ i))

theorem generatedBy_orbitCover {n : ℕ} (representative : Fin n → X)
    (hcover : ∀ x : X, ∃ (j : Fin n) (g : H), b g (representative j) = x) :
    RepresentationGeneratedBy
      (LinearSemidirectCoprimeSocleBounds.linearRepresentation (TernaryMonomialCocycle.linearAction b d hone hmul)) n := by
  let rho := LinearSemidirectCoprimeSocleBounds.linearRepresentation (TernaryMonomialCocycle.linearAction b d hone hmul)
  let code : Fin n → rho.asModule := fun j ↦
    rho.asModuleEquiv.symm (Pi.single (representative j) 1)
  let P : Submodule (ZMod 3)[H] rho.asModule :=
    Submodule.span (ZMod 3)[H] (Set.range code)
  let S : Subrepresentation rho := Subrepresentation.ofSubmodule' P
  have hdelta : ∀ x : X, (Pi.single x 1 : X → ZMod 3) ∈ S := by
    intro x
    obtain ⟨j, g, rfl⟩ := hcover x
    have hj : (Pi.single (representative j) 1 : X → ZMod 3) ∈ S := by
      change code j ∈ P
      exact Submodule.subset_span ⟨j, rfl⟩
    have hg := S.apply_mem_toSubmodule g hj
    change TernaryMonomialOrbitUniform.representation b d hone hmul g
      (Pi.single (representative j) 1) ∈ S at hg
    rw [TernaryMonomialOrbitUniform.single b d hone hmul] at hg
    have hm := S.toSubmodule.smul_mem ((d g (b g (representative j)))⁻¹) hg
    simpa only [mul_one, ← Pi.single_smul, smul_eq_mul,
      inv_mul_cancel₀ (TernaryMonomialOrbitUniform.coefficient_ne_zero b d hone hmul
        g (b g (representative j)))] using hm
  have hall (v : X → ZMod 3) : v ∈ S := by
    have hdecomp : (∑ i, v i • (Pi.single i 1 : X → ZMod 3)) = v := by
      calc
        (∑ i, v i • (Pi.single i 1 : X → ZMod 3)) = ∑ i, Pi.single i (v i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← Pi.single_smul]
          simp
        _ = v := LinearMap.sum_single_apply (fun _ : X ↦ ZMod 3) v
    rw [← hdecomp]
    exact S.toSubmodule.sum_mem fun i _ ↦ S.toSubmodule.smul_mem (v i) (hdelta i)
  refine ⟨code, top_unique ?_⟩
  intro x _
  exact hall x


end SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralTernaryOrbitGenerators
