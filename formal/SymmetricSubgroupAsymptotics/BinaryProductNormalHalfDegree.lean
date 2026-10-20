import SymmetricSubgroupAsymptotics.PrimePrimarySocleTypeSharing
import SymmetricSubgroupAsymptotics.PermutationTwoGroupRank

/-! The normal-generator half-degree bound on a literal product of binary
permutation factors. The proof uses the faithful disjoint-union action and
the proved binary permutation-character bound, with no literature input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryProductNormalHalfDegree

private theorem pi_isPGroup {I : Type} [Fintype I] (P : I → Type)
    [∀ i, Group (P i)] [∀ i, Finite (P i)]
    (hp : ∀ i, IsPGroup 2 (P i)) : IsPGroup 2 (∀ i, P i) := by
  choose n hn using fun i => (hp i).exists_card_eq
  apply IsPGroup.of_card (n := ∑ i, n i)
  rw [Nat.card_pi]
  simp_rw [hn]
  exact Finset.prod_pow_eq_pow_sum _ _ _

variable {I : Type} [Fintype I] (n : I → ℕ)
    (K : ∀ i, Subgroup (Equiv.Perm (Fin (n i))))

/-- The literal disjoint-union action, with each original point preserved. -/
def action : (∀ i, K i) →* Equiv.Perm (Σ i, Fin (n i)) where
  toFun g := {
    toFun x := ⟨x.1, (g x.1).1 x.2⟩
    invFun x := ⟨x.1, (g x.1).1.symm x.2⟩
    left_inv x := by rcases x with ⟨i, x⟩; simp
    right_inv x := by rcases x with ⟨i, x⟩; simp }
  map_one' := by apply Equiv.ext; rintro ⟨i, x⟩; rfl
  map_mul' _ _ := by apply Equiv.ext; rintro ⟨i, x⟩; rfl

/-- Faithfulness follows coordinatewise in the same original action. -/
theorem action_injective : Function.Injective (action n K) := by
  intro a b hab
  funext i
  apply Subtype.ext
  apply Equiv.ext
  intro x
  have he := Equiv.congr_fun hab (⟨i, x⟩ : Σ i, Fin (n i))
  exact eq_of_heq (Sigma.mk.inj_iff.mp he).2

/-- Every actual normal subgroup of the literal binary product has the
unconditional half-degree bound. No transitivity is needed. -/
theorem normalGen_le (hK : ∀ i, IsPGroup 2 (K i))
    (N : Subgroup (∀ i, K i)) [N.Normal] :
    (MarkedC4.normalGen N : ℝ) ≤ (∑ i : I, (n i : ℝ)) / 2 := by
  let X := Σ i, Fin (n i)
  let f := (action n K).comp N.subtype
  letI : MulAction N X := MulAction.compHom X f
  letI : FaithfulSMul N X := ⟨by
    intro a b hab
    apply Subtype.ext
    apply action_injective n K
    apply Equiv.ext
    exact hab⟩
  have hN : IsPGroup 2 N := (pi_isPGroup (fun i => K i) hK).to_subgroup N
  have hhead := permutationTwoGroup_primeCharacterRank_le N X hN
  have hgen := (MarkedC4.normalGen_normalSubgroup_le_primeCharacterRank 2 N hN).trans hhead
  have hcard : Nat.card X = ∑ i : I, n i := by
    rw [Nat.card_sigma]
    simp only [Nat.card_fin]
  rw [hcard] at hgen
  have htwo : 2 * MarkedC4.normalGen N ≤ ∑ i : I, n i := by omega
  have hreal : 2 * (MarkedC4.normalGen N : ℝ) ≤ ∑ i : I, (n i : ℝ) := by
    exact_mod_cast htwo
  linarith

end SymmetricSubgroupAsymptotics.BinaryProductNormalHalfDegree
