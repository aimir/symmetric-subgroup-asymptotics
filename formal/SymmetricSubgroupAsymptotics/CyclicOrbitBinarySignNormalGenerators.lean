import SymmetricSubgroupAsymptotics.LinearSemidirectUniformNormalGenerators
import SymmetricSubgroupAsymptotics.PermutationPolynomialOrbitGenerators
import SymmetricSubgroupAsymptotics.RepresentationDualSubquotientGenerators
import SymmetricSubgroupAsymptotics.NormalGeneratorQuotientSocles

/-! Binary sign modules inside a permutation module with one cyclic point
orbit. Every invariant sign subspace is uniformly cyclic, including the
even-sign subspace. Thus its actual semidirect product adds at most one
ambient normal generator to the original complement bound. No coprime
or splitting assertion about a separate literal permutation group is used. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CyclicOrbitBinarySignNormalGenerators

variable {R X : Type} [Group R] [MulAction R X] [Fintype X] [DecidableEq X]

abbrev permutationRepresentation := permutationFunctionRepresentation (ZMod 2) R X

variable (E : Subrepresentation (permutationRepresentation (R := R) (X := X)))

def linearAction : R →* (E.toSubmodule ≃ₗ[ZMod 2] E.toSubmodule) where
  toFun g :=
    { toFun := E.toRepresentation g
      invFun := E.toRepresentation g⁻¹
      left_inv := by
        intro v
        change (E.toRepresentation g⁻¹ * E.toRepresentation g) v = v
        rw [← map_mul,inv_mul_cancel,map_one]
        rfl
      right_inv := by
        intro v
        change (E.toRepresentation g * E.toRepresentation g⁻¹) v = v
        rw [← map_mul,mul_inv_cancel,map_one]
        rfl
      map_add' := (E.toRepresentation g).map_add
      map_smul' := (E.toRepresentation g).map_smul }
  map_one' := by
    apply LinearEquiv.ext
    intro v
    exact LinearMap.congr_fun E.toRepresentation.map_one v
  map_mul' g h := by
    apply LinearEquiv.ext
    intro v
    exact LinearMap.congr_fun (E.toRepresentation.map_mul g h) v

abbrev Model := LinearSemidirectCoprimeSocleBounds.Model (linearAction E)

theorem uniform (c : R) (x : X) (hcycle : ∀ y : X, ∃ n : ℕ, c^n • x = y) :
    UniformSubrepresentationGeneratorBound
      (LinearSemidirectCoprimeSocleBounds.linearRepresentation (linearAction E)) 1 := by
  have hfull : UniformSubrepresentationGeneratorBound
      (permutationRepresentation (R := R) (X := X)) 1 := by
    apply permutationFunctionRepresentation_uniform_of_polynomial_orbitCover
      c (fun _ : Fin 1 => x)
    intro y
    obtain ⟨n,hn⟩ := hcycle y
    exact ⟨0,n,hn⟩
  let inclusion : E.toRepresentation.IntertwiningMap
      (permutationRepresentation (R := R) (X := X)) :=
    { toLinearMap := E.toSubmodule.subtype
      isIntertwining' _ := rfl }
  change UniformSubrepresentationGeneratorBound E.toRepresentation 1
  exact hfull.of_injective inclusion (fun _ _ he => Subtype.ext he)

theorem normalGen_le [Finite R] (c : R) (x : X)
    (hcycle : ∀ y : X, ∃ n : ℕ, c^n • x = y)
    (a : ℕ) (hR : ∀ K : Subgroup R, K.Normal → MarkedC4.normalGen K ≤ a)
    (N : Subgroup (Model E)) [N.Normal] : MarkedC4.normalGen N ≤ 1+a :=
  LinearSemidirectUniformNormalGenerators.normalGen_le (linearAction E) 1 a
    (uniform E c x hcycle) hR N

theorem normal_generating_tuples [Finite R] (c : R) (x : X)
    (hcycle : ∀ y : X, ∃ n : ℕ, c^n • x = y)
    (a : ℕ) (hR : ∀ K : Subgroup R, K.Normal → MarkedC4.normalGen K ≤ a)
    (N : Subgroup (Model E)) (hN : N.Normal) :
    ∃ g : Fin (1+a) → Model E, Subgroup.normalClosure (Set.range g) = N := by
  letI := hN
  exact exists_normal_generating_tuple_of_normalGen_le N
    (normalGen_le E c x hcycle a hR N)

theorem quotientSocle [Finite R] (c : R) (x : X)
    (hcycle : ∀ y : X, ∃ n : ℕ, c^n • x = y)
    (a : ℕ) (hR : ∀ K : Subgroup R, K.Normal → MarkedC4.normalGen K ≤ a)
    (N : Subgroup (Model E)) [N.Normal] : SocleNormalGeneratorBound (Model E ⧸ N) (1+a) :=
  quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    (normal_generating_tuples E c x hcycle a hR) N

end SymmetricSubgroupAsymptotics.CyclicOrbitBinarySignNormalGenerators

end
