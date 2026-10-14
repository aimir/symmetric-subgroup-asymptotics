import SymmetricSubgroupAsymptotics.LinearSemidirectUniformNormalGenerators
import SymmetricSubgroupAsymptotics.PermutationPolynomialOrbitGenerators
import SymmetricSubgroupAsymptotics.C2WreathNormalCoverQuotient
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! The two-coordinate prime permutation module is uniformly cyclic under
the block exchange, including characteristic two. Consequently every
normal subgroup of C_p wr C_2 has two ambient normal generators. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimePairWreathNormalGenerators

open SemidirectProduct

abbrev Binary := Multiplicative (ZMod 2)
abbrev Vector (p : ℕ) := Fin 2 → ZMod p
abbrev Cyclic (p : ℕ) := Multiplicative (ZMod p)

def labels : Binary →* Equiv.Perm (Fin 2) where
  toFun c := if c = 1 then 1 else Equiv.swap 0 1
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

variable (p : ℕ) [Fact p.Prime]

def linearAction : Binary →* (Vector p ≃ₗ[ZMod p] Vector p) where
  toFun g :=
    { toFun := fun v i ↦ v (labels g⁻¹ i)
      invFun := fun v i ↦ v (labels g i)
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

abbrev Model := LinearSemidirectCoprimeSocleBounds.Model (linearAction p)

theorem uniform : UniformSubrepresentationGeneratorBound
    (LinearSemidirectCoprimeSocleBounds.linearRepresentation (linearAction p)) 1 := by
  letI : MulAction Binary (Fin 2) := MulAction.compHom (Fin 2) labels
  change UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod p) Binary (Fin 2)) 1
  apply permutationFunctionRepresentation_uniform_of_polynomial_orbitCover
    C2Wreath.gen (fun _ : Fin 1 ↦ 0)
  intro i
  fin_cases i
  · exact ⟨0, 0, by simp⟩
  · exact ⟨0, 1, by decide +kernel⟩

theorem model_normalGen_le (H : Subgroup (Model p)) (hH : H.Normal) :
    MarkedC4.normalGen H ≤ 2 := by
  letI := hH
  apply LinearSemidirectUniformNormalGenerators.normalGen_le (linearAction p) 1 1
    (uniform p) ?_ H
  intro K hK
  letI := hK
  exact CoprimeCyclicQuotientSocles.normalGen_le_one_of_isCyclic K

def coordinates : Multiplicative (Vector p) →* Cyclic p × Cyclic p where
  toFun v := (Multiplicative.ofAdd (v.toAdd 0), Multiplicative.ofAdd (v.toAdd 1))
  map_one' := rfl
  map_mul' _ _ := rfl

def toWreath : Model p →* C2Wreath.W (Cyclic p) :=
  SemidirectProduct.map (coordinates p) (MonoidHom.id Binary) (by
    intro c
    apply MonoidHom.ext
    intro v
    rcases C2Wreath.cases c with rfl | rfl
    · change coordinates p
          (LinearSemidirectCoprimeSocleBounds.linearAction (linearAction p) 1 v) =
        C2Wreath.swapAut (Cyclic p) 1 (coordinates p v)
      rw [map_one, C2Wreath.swapAut_one]
      rfl
    · change
        (Multiplicative.ofAdd (v.toAdd 1), Multiplicative.ofAdd (v.toAdd 0)) =
          C2Wreath.swapAut (Cyclic p) C2Wreath.gen (coordinates p v)
      rw [C2Wreath.swapAut_gen]
      rfl)

theorem toWreath_surjective : Function.Surjective (toWreath p) := by
  intro g
  refine ⟨⟨Multiplicative.ofAdd ![g.left.1.toAdd, g.left.2.toAdd], g.right⟩, ?_⟩
  apply SemidirectProduct.ext
  · rfl
  · rfl

theorem normal_generating_pairs (H : Subgroup (C2Wreath.W (Cyclic p)))
    (hH : H.Normal) :
    ∃ x : Fin 2 → C2Wreath.W (Cyclic p), Subgroup.normalClosure (Set.range x) = H := by
  apply normal_generating_tuples_of_surjective (toWreath p) (toWreath_surjective p) ?_ H hH
  intro N hN
  letI := hN
  exact exists_normal_generating_tuple_of_normalGen_le N (model_normalGen_le p N hN)

theorem of_prime_card {A : Type} [Group A] (hcard : Nat.card A = p)
    (H : Subgroup (C2Wreath.W A)) (hH : H.Normal) :
    ∃ x : Fin 2 → C2Wreath.W A, Subgroup.normalClosure (Set.range x) = H := by
  have hsource : Nat.card (Cyclic p) = p := by
    simp only [Cyclic, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  let e : Cyclic p ≃* A := mulEquivOfPrimeCardEq hsource hcard
  exact normal_generating_tuples_of_surjective (C2Wreath.mapLocal e.toMonoidHom)
    (C2Wreath.mapLocal_surjective e.toMonoidHom e.surjective)
    (normal_generating_pairs p) H hH

theorem quotientSocle_two (N : Subgroup (C2Wreath.W (Cyclic p))) [N.Normal] :
    SocleNormalGeneratorBound (C2Wreath.W (Cyclic p) ⧸ N) 2 :=
  quotientSocleNormalGeneratorBound_of_normal_generating_tuples (normal_generating_pairs p) N

end PrimePairWreathNormalGenerators
end SymmetricSubgroupAsymptotics

end
