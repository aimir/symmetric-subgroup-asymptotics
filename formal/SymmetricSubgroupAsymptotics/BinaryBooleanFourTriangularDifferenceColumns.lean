import SymmetricSubgroupAsymptotics.BinaryBooleanFourTriangularMonomialErrors
import SymmetricSubgroupAsymptotics.BinaryPairPolynomialPermutationDifference

/-! Genuine triangular point actions have the same leading derivative
columns as pure translations. The proof inducts on a monomial's highest
variable; every higher-bit error remains in its actual lower prefix. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates
open BinaryElementaryPairMonomialWidth
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private theorem flip_bit_value : ∀ (i j : Fin 4) (x : Fin 16),
    bitValue j (flipIndex i x) = if j = i then bitValue j x + 1 else bitValue j x := by decide

private theorem highest_variable_decomposition : ∀ a : Fin 16, a ≠ 0 →
    ∃ (j : Fin 4) (b : Fin 16), a = unionIndex (variableIndex j) b ∧
      b.val < 2 ^ j.val ∧ b < a := by decide

private theorem high_variable_above_selected : ∀ (i j : Fin 4) (b : Fin 16),
    b.val < 2 ^ j.val → ¬(unionIndex (variableIndex j) b).val < 2 ^ (i.val+1) → i < j := by decide

private theorem high_variable_block_bound : ∀ (i j : Fin 4) (b : Fin 16),
    i < j → b.val < 2 ^ j.val → 2 ^ j.val ≤ higherBlock i (unionIndex (variableIndex j) b) := by decide

theorem triangularMonomialError_zero_of_low
    (p : Equiv.Perm (Fin 16)) (i : Fin 4) (hp : FixesLowerFlips p i)
    (a : Fin 16) (ha : a.val < 2 ^ (i.val+1)) : triangularMonomialError p i a = 0 := by
  let r : Fin 5 := ⟨i.val+1, by have := i.isLt; omega⟩
  have hprefix := monomial_prefix_of_lt a r ha
  have he : (fun x => monomial (support a) (p x)) = translate i (monomial (support a)) := by
    funext x
    apply hprefix
    intro j hj
    rw [flip_bit_value]
    by_cases hji : j = i
    · subst j
      rw [if_pos rfl]
      exact (hp x).2
    · rw [if_neg hji]
      apply (hp x).1 j
      change j.val < i.val
      change j.val < i.val + 1 at hj
      have hne : j.val ≠ i.val := fun hv => hji (Fin.ext hv)
      omega
  unfold triangularMonomialError
  rw [he, ← evaluate_basis a]
  change derivative i (Pi.single a 1) - derivative i (Pi.single a 1) = 0
  exact sub_self _

theorem triangularMonomialError_coefficients_zero
    (p : Equiv.Perm (Fin 16)) (hp : IsTriangularPermutation p)
    (i : Fin 4) (hi : FixesLowerFlips p i) :
    ∀ a c : Fin 16, higherBlock i a ≤ c.val → triangularMonomialError p i a c = 0 := by
  suffices h : ∀ m (a : Fin 16), a.val = m → ∀ c : Fin 16,
      higherBlock i a ≤ c.val → triangularMonomialError p i a c = 0 from
    fun a c hc => h a.val a rfl c hc
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro a hval c hc
    by_cases hlow : a.val < 2 ^ (i.val+1)
    · rw [triangularMonomialError_zero_of_low p i hi a hlow]
      rfl
    · have hne : a ≠ 0 := by
        intro he
        apply hlow
        rw [he]
        exact pow_pos (by decide) _
      obtain ⟨j, b, ha, hb, hba⟩ := highest_variable_decomposition a hne
      have hij : i < j := high_variable_above_selected i j b hb (ha ▸ hlow)
      have hbError : ∀ d : Fin 16, higherBlock i b ≤ d.val → triangularMonomialError p i b d = 0 :=
        ih b.val (by change b.val < a.val at hba; omega) b rfl
      have hshift := monomialVariable_shift_higherBlock_error i j b hij hb
        (triangularMonomialError p i b) hbError c (ha ▸ hc)
      let r : Fin 5 := ⟨j.val, by have := j.isLt; omega⟩
      have hproduct : DependsOnPrefix
          ((fun x => bitValue j (p x) - bitValue j x) *
            (fun x => monomial (support b) (p x))) r.val :=
        prefix_mul (hp j) (prefix_comp_triangular (monomial_prefix_of_lt b r hb) p hp)
      have hblock : 2 ^ j.val ≤ c.val :=
        (high_variable_block_bound i j b hij hb).trans (ha ▸ hc)
      have hsecond := prefix_polynomial_coefficients_zero _ r hproduct c hblock
      rw [ha, triangularMonomialError_union_variable p i j b hij hb]
      change monomialMultiplier (variableIndex j) (triangularMonomialError p i b) c +
        evaluate ((fun x => bitValue j (p x) - bitValue j x) *
          (fun x => monomial (support b) (p x))) c = 0
      rw [hshift, hsecond, add_zero]

theorem triangular_permutation_difference_hasLeading
    (p : Equiv.Perm (Fin 16)) (hp : IsTriangularPermutation p)
    (i : Fin 4) (hi : FixesLowerFlips p i)
    (v : V) (a : Fin 16) (hv : FiniteRowLeadingWeight.HasLeading v a)
    (hia : i ∈ support a) :
    FiniteRowLeadingWeight.HasLeading (permutationDifference p.symm v) (removeIndex i a) := by
  apply triangular_derivative_hasLeading (permutationDifference p.symm) i _ v a hv hia
  intro b c hc
  have he := triangularMonomialError_coefficients_zero p hp i hi b c hc
  change evaluate ((fun x => monomial (support b) (p x)) - monomial (support b)) c -
    derivative i (Pi.single b 1) c = 0 at he
  apply sub_eq_zero.mp
  simpa only [permutationDifference, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.id_apply, evaluate_basis, evaluate_monomial, reindex, Equiv.symm_symm, map_sub] using he

end SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates
