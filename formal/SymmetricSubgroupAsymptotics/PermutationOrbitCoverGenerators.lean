import SymmetricSubgroupAsymptotics.RepresentationGeneratorRestrictionMaschke
import SymmetricSubgroupAsymptotics.PermutationSubrepresentationHead
import Mathlib.LinearAlgebra.Pi

/-!
# Uniform natural-module generators from a small orbit cover

One delta function per orbit generates a permutation representation. If
the acting group has invertible order, Maschke makes that bound uniform.
A homomorphism from such a group into a larger top therefore certifies the
larger top's uniform bound using only an orbit cover on the point set.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra BigOperators

namespace SymmetricSubgroupAsymptotics

variable {k G L X : Type} [Field k] [Group G] [Group L]
  [Fintype X] [DecidableEq X] [MulAction G X]

omit [Fintype X] in
/-- Delta functions transform by the original point action. -/
theorem permutationFunctionRepresentation_single (g : G) (x : X) :
    permutationFunctionRepresentation k G X g (Pi.single x 1) =
      Pi.single (g • x) 1 := by
  ext y
  simp [permutationFunctionRepresentation_apply, Pi.single_apply, inv_smul_eq_iff]

/-- A displayed point-orbit cover gives the corresponding number of
module generators for the natural permutation representation. -/
theorem permutationFunctionRepresentation_generatedBy_orbitCover
    {n : ℕ} (representative : Fin n → X)
    (hcover : ∀ x : X, ∃ (j : Fin n) (g : G), g • representative j = x) :
    RepresentationGeneratedBy (permutationFunctionRepresentation k G X) n := by
  let rho := permutationFunctionRepresentation k G X
  let code : Fin n → rho.asModule := fun j ↦
    rho.asModuleEquiv.symm (Pi.single (representative j) 1)
  let P : Submodule k[G] rho.asModule := Submodule.span k[G] (Set.range code)
  let S : Subrepresentation rho := Subrepresentation.ofSubmodule' P
  have hdelta : ∀ x : X, (Pi.single x 1 : X → k) ∈ S := by
    intro x
    obtain ⟨j, g, rfl⟩ := hcover x
    rw [← permutationFunctionRepresentation_single]
    apply S.apply_mem_toSubmodule
    change code j ∈ P
    exact Submodule.subset_span ⟨j, rfl⟩
  have hall : ∀ v : X → k, v ∈ S := by
    intro v
    have hdecomp : (∑ i, v i • (Pi.single i 1 : X → k)) = v := by
      calc
        (∑ i, v i • (Pi.single i 1 : X → k)) = ∑ i, Pi.single i (v i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← Pi.single_smul]
          simp
        _ = v := LinearMap.sum_single_apply (fun _ : X ↦ k) v
    rw [← hdecomp]
    exact S.toSubmodule.sum_mem fun i _ ↦ S.toSubmodule.smul_mem (v i) (hdelta i)
  refine ⟨code, top_unique ?_⟩
  intro x _
  exact hall x

/-- In invertible characteristic, a point-orbit cover uniformly generates
every invariant subspace. -/
theorem permutationFunctionRepresentation_uniform_of_invertible_orbitCover
    [Finite G] [NeZero (Nat.card G : k)]
    {n : ℕ} (representative : Fin n → X)
    (hcover : ∀ x : X, ∃ (j : Fin n) (g : G), g • representative j = x) :
    UniformSubrepresentationGeneratorBound (permutationFunctionRepresentation k G X) n :=
  RepresentationGeneratedBy.uniform_of_invertible_order _
    (permutationFunctionRepresentation_generatedBy_orbitCover representative hcover)

/-- A finite subgroup or homomorphic image of invertible order with an
`n`-place point-orbit cover certifies the whole top's uniform module bound.
Only the displayed point action is checked; no vector-state census occurs. -/
theorem permutationFunctionRepresentation_uniform_of_restricted_orbitCover
    [Finite L] [NeZero (Nat.card L : k)]
    (f : L →* G) {n : ℕ} (representative : Fin n → X)
    (hcover : ∀ x : X, ∃ (j : Fin n) (g : L), f g • representative j = x) :
    UniformSubrepresentationGeneratorBound (permutationFunctionRepresentation k G X) n := by
  letI : MulAction L X := MulAction.compHom X f
  have hrestricted : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation k L X) n :=
    permutationFunctionRepresentation_uniform_of_invertible_orbitCover representative hcover
  have hrep : permutationFunctionRepresentation k L X =
      (permutationFunctionRepresentation k G X).comp f := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    funext x
    change v (f (g⁻¹) • x) = v ((f g)⁻¹ • x)
    rw [map_inv]
  apply UniformSubrepresentationGeneratorBound.of_comp
    (permutationFunctionRepresentation k G X) f
  rw [← hrep]
  exact hrestricted

end SymmetricSubgroupAsymptotics

end
