import SymmetricSubgroupAsymptotics.TernaryMonomialSemidirect
import Mathlib.LinearAlgebra.Pi

/-! An invertible scalar character does not change the number of delta
generators needed by a permutation action. One delta per displayed block
orbit generates the whole monomial module. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra BigOperators

namespace SymmetricSubgroupAsymptotics
namespace TernaryMonomialOrbitGenerators

open TernaryMonomialSemidirect

variable {H X : Type} [Group H] [Fintype X] [DecidableEq X]
  (b : H →* Equiv.Perm X) (s : H →* (ZMod 3)ˣ)

theorem single_action (g : H) (x : X) :
    linearAction b s g (Pi.single x 1) =
      coefficient s g • (Pi.single (b g x) 1 : X → ZMod 3) := by
  funext y
  change coefficient s g * (Pi.single x 1 : X → ZMod 3) (b g⁻¹ y) =
    coefficient s g * (Pi.single (b g x) 1 : X → ZMod 3) y
  have hi : b g⁻¹ (b g x) = x := by
    rw [map_inv]
    exact (b g).symm_apply_apply x
  by_cases he : y = b g x
  · subst y
    rw [hi, Pi.single_eq_same, Pi.single_eq_same]
  · have hn : b g⁻¹ y ≠ x := by
      intro hy
      apply he
      calc
        y = b g (b g⁻¹ y) := by rw [map_inv]; exact ((b g).apply_symm_apply y).symm
        _ = b g x := congrArg (b g) hy
    rw [Pi.single_eq_of_ne hn, Pi.single_eq_of_ne he]

theorem generatedBy_orbitCover {n : ℕ} (representative : Fin n → X)
    (hcover : ∀ x : X, ∃ (j : Fin n) (g : H), b g (representative j) = x) :
    RepresentationGeneratedBy
      (LinearSemidirectCoprimeSocleBounds.linearRepresentation (linearAction b s)) n := by
  let rho := LinearSemidirectCoprimeSocleBounds.linearRepresentation (linearAction b s)
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
    change linearAction b s g (Pi.single (representative j) 1) ∈ S at hg
    rw [single_action] at hg
    have hm := S.toSubmodule.smul_mem (coefficient s g⁻¹) hg
    have hc : coefficient s g⁻¹ * coefficient s g = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    simpa only [smul_smul, hc, one_smul] using hm
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

end TernaryMonomialOrbitGenerators
end SymmetricSubgroupAsymptotics

end
