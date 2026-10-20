import SymmetricSubgroupAsymptotics.LinearSemidirectUniformNormalGenerators
import SymmetricSubgroupAsymptotics.PermutationPolynomialOrbitGenerators
import SymmetricSubgroupAsymptotics.TernaryFourBlockMetacyclicModel

/-!
# Normal generators in two-sign complements

The binary kernel is the actual two-coordinate permutation module.
A rotation swapping its coordinates proves uniform module generation by
one even though the complement order is even. Thus adjoining this kernel
adds one to the complement's ambient normal-generator bound. The two
concrete bases below are C4 and D8; no complement normal subgroups are
enumerated.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryPermutationSemidirectNormalGenerators

abbrev Vector := Fin 2 → ZMod 2

def linearAction {R : Type} [Group R] (p : R →* Equiv.Perm (Fin 2)) :
    R →* (Vector ≃ₗ[ZMod 2] Vector) where
  toFun g :=
    { toFun := fun v i ↦ v (p g⁻¹ i)
      invFun := fun v i ↦ v (p g i)
      left_inv := by intro v; funext i; simp
      right_inv := by intro v; funext i; simp
      map_add' := by intro v w; rfl
      map_smul' := by intro a v; rfl }
  map_one' := by apply LinearEquiv.ext; intro v; funext i; simp
  map_mul' := by
    intro g h
    apply LinearEquiv.ext
    intro v
    funext i
    simp [mul_inv_rev]

abbrev Model {R : Type} [Group R] (p : R →* Equiv.Perm (Fin 2)) :=
  LinearSemidirectCoprimeSocleBounds.Model (linearAction p)

theorem uniform {R : Type} [Group R] (p : R →* Equiv.Perm (Fin 2))
    (g : R) (hg : p g 0 = 1) :
    UniformSubrepresentationGeneratorBound
      (LinearSemidirectCoprimeSocleBounds.linearRepresentation (linearAction p)) 1 := by
  letI : MulAction R (Fin 2) := MulAction.compHom (Fin 2) p
  change UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) R (Fin 2)) 1
  apply permutationFunctionRepresentation_uniform_of_polynomial_orbitCover g (fun _ : Fin 1 ↦ 0)
  intro i
  fin_cases i
  · exact ⟨0, 0, by simp⟩
  · exact ⟨0, 1, by simpa only [pow_one] using hg⟩

theorem normalGen_le {R : Type} [Group R] [Finite R]
    (p : R →* Equiv.Perm (Fin 2)) (g : R) (hg : p g 0 = 1)
    (a : ℕ) (hR : ∀ K : Subgroup R, K.Normal → MarkedC4.normalGen K ≤ a)
    (H : Subgroup (Model p)) (hH : H.Normal) : MarkedC4.normalGen H ≤ 1 + a := by
  letI := hH
  exact LinearSemidirectUniformNormalGenerators.normalGen_le (linearAction p) 1 a
    (uniform p g hg) hR H

open PrimitiveAffineDegreeTwoTwelveRow131AffineModel (Block)
open TernaryFourBlockMetacyclicModel (Complement)

def cyclicLabels : Block →* Equiv.Perm (Fin 2) where
  toFun c := if c.toAdd.val % 2 = 0 then 1 else Equiv.swap 0 1
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

def dihedralLabels : Complement true →* Equiv.Perm (Fin 2) where
  toFun g := cyclicLabels g.left
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

abbrev CyclicModel := Model cyclicLabels
abbrev DihedralModel := Model dihedralLabels

theorem cyclic_normalGen (H : Subgroup CyclicModel) (hH : H.Normal) :
    MarkedC4.normalGen H ≤ 2 := by
  apply normalGen_le cyclicLabels (Multiplicative.ofAdd 1) (by decide +kernel) 1 ?_ H hH
  intro K hK
  letI := hK
  exact CoprimeCyclicQuotientSocles.normalGen_le_one_of_isCyclic K

theorem dihedral_normalGen (H : Subgroup DihedralModel) (hH : H.Normal) :
    MarkedC4.normalGen H ≤ 3 :=
  normalGen_le dihedralLabels
    (SemidirectProduct.inl (Multiplicative.ofAdd 1)) (by decide +kernel) 2
    (TernaryFourBlockMetacyclicModel.complement_normalGen true) H hH

theorem cyclic_card : Nat.card CyclicModel = 16 := by
  rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
  have hV : Nat.card (Multiplicative Vector) = 4 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have hB : Nat.card Block = 4 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  rw [hV, hB]

theorem dihedral_card : Nat.card DihedralModel = 32 := by
  rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
  have hV : Nat.card (Multiplicative Vector) = 4 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have hB : Nat.card (Complement true) = 8 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  rw [hV, hB]

end BinaryPermutationSemidirectNormalGenerators
end SymmetricSubgroupAsymptotics

end
