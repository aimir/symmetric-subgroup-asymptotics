import SymmetricSubgroupAsymptotics.ActualLocalChiefHead
import SymmetricSubgroupAsymptotics.PermutationChiefWeight

/-! The relative ternary head of an original normal subgroup is bounded
by the genuine weight of any chosen chief series of its original ambient
group. This is the index-one instance of the actual local-chief theorem:
the evaluation is the original inclusion and the ambient map is identity.
No primitive estimate or composition-length identification is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

@[simp] theorem ternaryIndexWidth_one : ternaryIndexWidth 1 = 1 := by
  norm_num [ternaryIndexWidth, ternaryWidthEnvelope, ternaryWidthCore,
    largestPrimePower]

theorem primeRelativeHead_le_actualChiefWeight
    {A : Type} [Group A] [Finite A]
    (N : Subgroup A) [N.Normal] (c : ActualChiefSeries A) :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤
      actualChiefSeriesTernaryWeight c := by
  have hconj : ∀ (h : (⊤ : Subgroup A)) (n : N),
      N.subtype (MulAut.conjNormal (h : A) n) =
        (⊤ : Subgroup A).subtype h * N.subtype n *
          ((⊤ : Subgroup A).subtype h)⁻¹ := by
    intro h n
    rfl
  have honto : Function.Surjective (⊤ : Subgroup A).subtype := by
    intro a
    exact ⟨⟨a, Subgroup.mem_top a⟩, rfl⟩
  have hsep : ∀ n : N,
      (∀ a : A, N.subtype (MulAut.conjNormal a n) = 1) → n = 1 := by
    intro n hn
    apply Subtype.ext
    have h := hn 1
    change (1 : A) * (n : A) * (1 : A)⁻¹ = 1 at h
    simpa only [one_mul, inv_one, mul_one] using h
  have h := actualLocalChiefHead_bound N (⊤ : Subgroup A) N.subtype
    (⊤ : Subgroup A).subtype hconj honto hsep c
  rw [Subgroup.index_top, ternaryIndexWidth_one, Nat.cast_one, mul_one] at h
  exact_mod_cast h

theorem primeRelativeHead_eq_zero_of_actualChiefWeight_zero
    {A : Type} [Group A] [Finite A]
    (N : Subgroup A) [N.Normal] (c : ActualChiefSeries A)
    (hc : actualChiefSeriesTernaryWeight c = 0) :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa only [hc] using primeRelativeHead_le_actualChiefWeight N c

variable {X : Type} [Finite X]

/-- Lagrange's theorem applies to the actual permutation ambient group;
the original normal subgroup and its ambient conjugation are retained. -/
theorem permutationRelativeHead_le_factorial
    (U : Subgroup (Equiv.Perm X)) (N : Subgroup U) [N.Normal] :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤
      ((Nat.card X).factorial).factorization 3 :=
  (primeRelativeHead_le_actualChiefWeight N (actualChiefSeries U)).trans
    (permutationChiefWeight_le_factorial U (actualChiefSeries U))

theorem permutationRelativeHead_eq_zero_of_card_le_two
    (U : Subgroup (Equiv.Perm X)) (N : Subgroup U) [N.Normal]
    (hX : Nat.card X ≤ 2) :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 0 :=
  primeRelativeHead_eq_zero_of_actualChiefWeight_zero N (actualChiefSeries U)
    (permutationChiefWeight_eq_zero_of_card_le_two U (actualChiefSeries U) hX)

theorem permutationRelativeHead_le_one_of_card_le_five
    (U : Subgroup (Equiv.Perm X)) (N : Subgroup U) [N.Normal]
    (hX : Nat.card X ≤ 5) :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤ 1 :=
  (primeRelativeHead_le_actualChiefWeight N (actualChiefSeries U)).trans
    (permutationChiefWeight_le_one_of_card_le_five U (actualChiefSeries U) hX)

theorem permutationRelativeHead_le_two_of_card_le_eight
    (U : Subgroup (Equiv.Perm X)) (N : Subgroup U) [N.Normal]
    (hX : Nat.card X ≤ 8) :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤ 2 :=
  (primeRelativeHead_le_actualChiefWeight N (actualChiefSeries U)).trans
    (permutationChiefWeight_le_two_of_card_le_eight U (actualChiefSeries U) hX)

end SymmetricSubgroupAsymptotics
