import SymmetricSubgroupAsymptotics.PermutationThreeGroupRank
import SymmetricSubgroupAsymptotics.TernaryIndexWidthValues

/-!
# Sharp elementary heads of transitive ternary groups

Iterating the literal three-block cover gives a sharper character-rank
bound than the general one-third permutation estimate.  At each step the
top is the actual faithful transitive action on the block set, while the
literal block kernel contributes the already proved `ternaryIndexWidth`.

This is the simultaneous-head input in the classification-free ternary
quotient recursion.  In particular, degrees `3`, `9`, and `27` have bounds
`1`, `2`, and `5`.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- The intrinsic head bound obtained by repeatedly taking literal blocks
of size three. -/
def ternaryTransitiveCharacterBound : ℕ → ℕ
  | 0 => 0
  | k + 1 => ternaryTransitiveCharacterBound k + ternaryIndexWidth (3 ^ k)

@[simp] theorem ternaryTransitiveCharacterBound_zero :
    ternaryTransitiveCharacterBound 0 = 0 := rfl

@[simp] theorem ternaryTransitiveCharacterBound_succ (k : ℕ) :
    ternaryTransitiveCharacterBound (k + 1) =
      ternaryTransitiveCharacterBound k + ternaryIndexWidth (3 ^ k) := rfl

@[simp] theorem ternaryTransitiveCharacterBound_one :
    ternaryTransitiveCharacterBound 1 = 1 := by
  norm_num [ternaryTransitiveCharacterBound]

@[simp] theorem ternaryTransitiveCharacterBound_two :
    ternaryTransitiveCharacterBound 2 = 2 := by
  norm_num [ternaryTransitiveCharacterBound]

@[simp] theorem ternaryTransitiveCharacterBound_three :
    ternaryTransitiveCharacterBound 3 = 5 := by
  norm_num [ternaryTransitiveCharacterBound]

/-- Every finite faithful transitive ternary group of degree `3^k` has
elementary ternary quotient rank at most the iterated block-head bound. -/
theorem transitiveThreeGroup_primeCharacterRank_le_power
    (k : ℕ) {X : Type} [Finite X]
    (U : Subgroup (Equiv.Perm X)) [MulAction.IsPretransitive U X]
    (hU : IsPGroup 3 U) (hdegree : Nat.card X = 3 ^ k) :
    Module.finrank (ZMod 3) (PrimeCharacters 3 U) ≤
      ternaryTransitiveCharacterBound k := by
  induction k generalizing X with
  | zero =>
      have hcard : Nat.card X ≤ 1 := by simpa using hdegree.le
      letI : Subsingleton X := Finite.card_le_one_iff_subsingleton.mp hcard
      simpa only [ternaryTransitiveCharacterBound_zero] using
        (primeCharacterRank_eq_zero_of_subsingleton_faithful_action
          (p := 3) (G := U) (X := X)).le
  | succ k ih =>
      have hcard : 1 < Nat.card X := by
        rw [hdegree]
        exact one_lt_pow' (by norm_num : 1 < (3 : ℕ)) (by omega)
      letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp hcard
      let x : X := Classical.choice (inferInstance : Nonempty X)
      obtain ⟨D⟩ := transitiveThreeBlockCover_nonempty U hU x
      have hpoints : Nat.card D.Points = 3 ^ k := by
        have hproduct := D.degree_product
        rw [hdegree, pow_succ] at hproduct
        omega
      have hext : Module.finrank (ZMod 3) (PrimeCharacters 3 U) ≤
          Module.finrank (ZMod 3) (PrimeCharacters 3 D.Top) +
            Module.finrank (ZMod 3)
              (primeRelativeCharacters 3 D.topMap.ker) := by
        have hdim (K L : Subgroup U) [K.Normal] [L.Normal] (h : K = L) :
            Module.finrank (ZMod 3) (primeRelativeCharacters 3 K) =
              Module.finrank (ZMod 3) (primeRelativeCharacters 3 L) := by
          subst L
          rfl
        have hker := hdim D.topMap.rangeRestrict.ker D.topMap.ker
          (MonoidHom.ker_rangeRestrict D.topMap)
        have h := primeCharacterRank_extension_le 3 D.topMap.rangeRestrict
          D.topMap.rangeRestrict_surjective
        rwa [hker] at h
      letI : MulAction.IsPretransitive D.Top D.Points := D.top_pretransitive
      letI : FaithfulSMul D.Top D.Points := D.top_faithful
      letI : Finite D.Top := D.top_finite
      have htop : Module.finrank (ZMod 3) (PrimeCharacters 3 D.Top) ≤
          ternaryTransitiveCharacterBound k :=
        ih D.Top (D.top_isPGroup hU) hpoints
      have hkernel : Module.finrank (ZMod 3)
          (primeRelativeCharacters 3 D.topMap.ker) ≤
            ternaryIndexWidth (3 ^ k) := by
        simpa only [hpoints] using D.kernel_relativeHead_le_indexWidth
      exact hext.trans <| by
        simpa only [ternaryTransitiveCharacterBound_succ] using
          Nat.add_le_add htop hkernel

/-- The sharp degree-three endpoint. -/
theorem transitiveThreeGroup_primeCharacterRank_le_one
    {X : Type} [Finite X]
    (U : Subgroup (Equiv.Perm X)) [MulAction.IsPretransitive U X]
    (hU : IsPGroup 3 U) (hdegree : Nat.card X = 3) :
    Module.finrank (ZMod 3) (PrimeCharacters 3 U) ≤ 1 := by
  simpa only [pow_one, ternaryTransitiveCharacterBound_one] using
    transitiveThreeGroup_primeCharacterRank_le_power 1 U hU hdegree

/-- The sharp degree-nine endpoint. -/
theorem transitiveThreeGroup_primeCharacterRank_le_two
    {X : Type} [Finite X]
    (U : Subgroup (Equiv.Perm X)) [MulAction.IsPretransitive U X]
    (hU : IsPGroup 3 U) (hdegree : Nat.card X = 9) :
    Module.finrank (ZMod 3) (PrimeCharacters 3 U) ≤ 2 := by
  have hpow : (3 : ℕ) ^ 2 = 9 := by norm_num
  simpa only [hpow, ternaryTransitiveCharacterBound_two] using
    transitiveThreeGroup_primeCharacterRank_le_power 2 U hU hdegree

/-- The sharp degree-twenty-seven endpoint used by the unrestricted row. -/
theorem transitiveThreeGroup_primeCharacterRank_le_five
    {X : Type} [Finite X]
    (U : Subgroup (Equiv.Perm X)) [MulAction.IsPretransitive U X]
    (hU : IsPGroup 3 U) (hdegree : Nat.card X = 27) :
    Module.finrank (ZMod 3) (PrimeCharacters 3 U) ≤ 5 := by
  have hpow : (3 : ℕ) ^ 3 = 27 := by norm_num
  simpa only [hpow, ternaryTransitiveCharacterBound_three] using
    transitiveThreeGroup_primeCharacterRank_le_power 3 U hU hdegree

end SymmetricSubgroupAsymptotics

end
