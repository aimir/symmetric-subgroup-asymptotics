import SymmetricSubgroupAsymptotics.PrimeRelativeRadical

/-! The literal kernel of a whole-group invariant character on an original
normal subgroup. Its normality is in the whole original ambient group.
For a nonzero character the original subgroup has index p over this kernel;
neither a chosen quotient model nor an order premise is used. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal]

def primeRelativeCharacterKernel (χ : primeRelativeCharacters p N) : Subgroup G :=
  (AddMonoidHom.toMultiplicativeRight χ.1).ker.map N.subtype

theorem primeRelativeCharacterKernel_le (χ : primeRelativeCharacters p N) :
    primeRelativeCharacterKernel p N χ ≤ N := by
  rintro x ⟨n, hn, rfl⟩
  exact n.2

@[simp] theorem coe_mem_primeRelativeCharacterKernel_iff
    (χ : primeRelativeCharacters p N) (n : N) :
    (n : G) ∈ primeRelativeCharacterKernel p N χ ↔ χ.1 (Additive.ofMul n) = 0 := by
  constructor
  · rintro ⟨m, hm, he⟩
    have hmn : m = n := Subtype.ext he
    exact hmn ▸ hm
  · exact fun hn => ⟨n, hn, rfl⟩

instance primeRelativeCharacterKernel_normal (χ : primeRelativeCharacters p N) :
    (primeRelativeCharacterKernel p N χ).Normal := ⟨by
  rintro x ⟨n, hn, rfl⟩ g
  refine ⟨⟨g * (n : G) * g⁻¹, Subgroup.Normal.conj_mem inferInstance _ n.2 g⟩, ?_, rfl⟩
  change χ.1 (Additive.ofMul
    (⟨g * (n : G) * g⁻¹, Subgroup.Normal.conj_mem inferInstance _ n.2 g⟩ : N)) = 0
  rw [χ.2 g n]
  exact hn⟩

theorem primeRelativeRadical_le_characterKernel (χ : primeRelativeCharacters p N) :
    primeRelativeRadical p N ≤ primeRelativeCharacterKernel p N χ :=
  primeRelativeRadical_le_mapped_character_ker p N χ

variable [Finite G]

/-- Nonzero original scalar characters are onto the same prime field. -/
theorem primeRelativeCharacter_surjective (χ : primeRelativeCharacters p N) (hχ : χ ≠ 0) :
    Function.Surjective χ.1 := by
  have hlinear : primeAbelianizationLift p N χ.1 ≠ 0 := by
    intro hz
    apply hχ
    apply Subtype.ext
    ext n
    have h := primeAbelianizationLift_apply p N χ.1 n
    rw [hz, LinearMap.zero_apply] at h
    exact h.symm
  intro z
  obtain ⟨v, hv⟩ := LinearMap.surjective hlinear z
  obtain ⟨n, hn⟩ := primeAbelianizationMap_surjective p N v
  refine ⟨n, ?_⟩
  rw [← primeAbelianizationLift_apply p N χ.1 n, hn]
  exact hv

theorem primeRelativeCharacter_quotient_card (χ : primeRelativeCharacters p N) (hχ : χ ≠ 0) :
    Nat.card (N ⧸ (AddMonoidHom.toMultiplicativeRight χ.1).ker) = p := by
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
    (AddMonoidHom.toMultiplicativeRight χ.1)
    (primeRelativeCharacter_surjective p N χ hχ)).toEquiv]
  exact Nat.card_zmod p

/-- Exact index p uses the kernel as an actual subgroup of the original G. -/
theorem primeRelativeCharacterKernel_card_factorization
    (χ : primeRelativeCharacters p N) (hχ : χ ≠ 0) :
    p * Nat.card (primeRelativeCharacterKernel p N χ) = Nat.card N := by
  have he : Nat.card (AddMonoidHom.toMultiplicativeRight χ.1).ker =
      Nat.card (primeRelativeCharacterKernel p N χ) :=
    Nat.card_congr ((AddMonoidHom.toMultiplicativeRight χ.1).ker.equivMapOfInjective
      N.subtype N.subtype_injective).toEquiv
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (AddMonoidHom.toMultiplicativeRight χ.1).ker
  rw [primeRelativeCharacter_quotient_card p N χ hχ, he] at hc
  exact hc.symm

end SymmetricSubgroupAsymptotics
