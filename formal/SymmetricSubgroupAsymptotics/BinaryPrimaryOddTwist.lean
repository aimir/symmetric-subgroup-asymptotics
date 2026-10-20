import SymmetricSubgroupAsymptotics.BinaryPrimaryLinearCharacter

/-!
# Coprime odd twists of a binary-primary linear character

Multiplying a binary-primary character by an odd-order character takes
the intersection of their kernels. In particular, a cubic character with
binary kernel turns the designated binary-primary prefix into an ordinary
linear anchor with binary kernel, preserving its central binary residual.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {G A : Type*} [Group G] [Finite G] [CommGroup A]

omit [Finite G] in
/-- Coprime exponents prevent cancellation between the two characters. -/
theorem binaryPrimary_mul_odd_ker (χ ψ : G →* A)
    (hχ : IsPGroup 2 χ.range) (n : ℕ) (hn : Nat.Coprime 2 n)
    (hψ : ∀ g : G, (ψ g) ^ n = 1) :
    (χ * ψ).ker = χ.ker ⊓ ψ.ker := by
  ext g
  change χ g * ψ g = 1 ↔ χ g = 1 ∧ ψ g = 1
  constructor
  · intro h
    have hinv : χ g = (ψ g)⁻¹ := mul_eq_one_iff_eq_inv.mp h
    have hnχ : (χ g) ^ n = 1 := by rw [hinv, inv_pow, hψ, inv_one]
    obtain ⟨a, ha⟩ := hχ ⟨χ g, ⟨g, rfl⟩⟩
    have htwo : (χ g) ^ (2 ^ a) = 1 := congrArg Subtype.val ha
    have hχone : χ g = 1 := orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (hn.pow_left a)
        (orderOf_dvd_of_pow_eq_one htwo) (orderOf_dvd_of_pow_eq_one hnχ))
    exact ⟨hχone, by simpa only [hχone, one_mul] using h⟩
  · rintro ⟨hχone, hψone⟩
    rw [hχone, hψone, one_mul]

omit [Finite G] in
/-- A character of odd exponent is trivial on all involutions. -/
theorem oddCharacter_apply_of_square_eq_one (ψ : G →* A)
    (n : ℕ) (hn : Nat.Coprime 2 n)
    (hψ : ∀ g : G, (ψ g) ^ n = 1) (z : G) (hz : z ^ 2 = 1) :
    ψ z = 1 := by
  have htwo : (ψ z) ^ 2 = 1 := by rw [← map_pow, hz, map_one]
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hn
      (orderOf_dvd_of_pow_eq_one htwo) (orderOf_dvd_of_pow_eq_one (hψ z)))

/-- The odd twist preserves the exact residual central binary subspace. -/
theorem binaryCentralOmegaSubmodule_odd_twist (χ ψ : G →* A)
    (n : ℕ) (hn : Nat.Coprime 2 n)
    (hψ : ∀ g : G, (ψ g) ^ n = 1) :
    binaryCentralOmegaSubmodule (χ * ψ).ker =
      binaryCentralOmegaSubmodule χ.ker := by
  ext z
  change χ (binaryCentralOmegaEmbedding z.toMul) *
      ψ (binaryCentralOmegaEmbedding z.toMul) = 1 ↔
    χ (binaryCentralOmegaEmbedding z.toMul) = 1
  rw [oddCharacter_apply_of_square_eq_one ψ n hn hψ
    (binaryCentralOmegaEmbedding z.toMul)
    (binaryCentralOmegaEquiv G z.toMul).property.2, mul_one]

/-- When the odd character already has binary kernel, its twist with a
binary-primary character has binary kernel too. -/
theorem binaryPrimary_mul_odd_kernel_isPGroup (χ ψ : G →* A)
    (hχ : IsPGroup 2 χ.range) (n : ℕ) (hn : Nat.Coprime 2 n)
    (hψ : ∀ g : G, (ψ g) ^ n = 1) (hker : IsPGroup 2 ψ.ker) :
    IsPGroup 2 (χ * ψ).ker := by
  have hle : (χ * ψ).ker ≤ ψ.ker := by
    rw [binaryPrimary_mul_odd_ker χ ψ hχ n hn hψ]
    exact inf_le_right
  exact hker.of_injective (Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)

/-- A supplied odd anchor and the two central-rank bounds produce the
ordinary linear prefix. The odd anchor is an explicit input: this theorem
does not assert the existence of a cubic quotient. -/
theorem exists_oddTwistedLinearCharacter_residual_rank_le
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    (ψ : G →* kˣ) (n : ℕ) (hn : Nat.Coprime 2 n)
    (hψ : ∀ g : G, (ψ g) ^ n = 1) (hker : IsPGroup 2 ψ.ker)
    (r : ℕ)
    (hcentral : Module.finrank (ZMod 2) (Additive (binaryCentralOmega G)) ≤ r + 1)
    (hderived : Module.finrank (ZMod 2)
      (binaryCentralOmegaSubmodule (commutator G)) ≤ r) :
    ∃ ξ : G →* kˣ, IsPGroup 2 ξ.ker ∧
      Module.finrank (ZMod 2) (binaryCentralOmegaSubmodule ξ.ker) ≤ r := by
  obtain ⟨χ, hχ, hresidual⟩ :=
    exists_binaryPrimaryLinearCharacter_residual_rank_le (k := k)
      r hcentral hderived
  refine ⟨χ * ψ,
    binaryPrimary_mul_odd_kernel_isPGroup χ ψ hχ n hn hψ hker, ?_⟩
  rw [binaryCentralOmegaSubmodule_odd_twist χ ψ n hn hψ]
  exact hresidual

end SymmetricSubgroupAsymptotics
