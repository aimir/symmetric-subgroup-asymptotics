import SymmetricSubgroupAsymptotics.BinaryCentralOmegaDetection
import Mathlib.GroupTheory.Abelianization.Finite
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega

/-!
# Binary-primary linear characters and residual central involutions

A central involution outside the derived subgroup can be detected by a
linear character with binary-primary image. The character is first chosen
on the full abelianization and then raised to the odd part of the group
order. In particular, its values are not restricted to signs: detecting
the square of an element of order four requires a fourth root of unity.

The residual rank statement concerns the literal central involutions in
the kernel. No character feasibility or normal-generator theorem is
assumed here.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {G A : Type*} [Group G] [Finite G] [CommGroup A]

/-- Remove the odd-primary part of a finite-image character. -/
def binaryPrimaryPart (χ : G →* A) : G →* A :=
  χ ^ (ordCompl[2] (Nat.card G))

omit [Finite G] in
theorem binaryPrimaryPart_isPGroup (χ : G →* A) :
    IsPGroup 2 (binaryPrimaryPart χ).range := by
  rintro ⟨a, ha⟩
  obtain ⟨g, rfl⟩ := ha
  refine ⟨(Nat.card G).factorization 2, Subtype.ext ?_⟩
  change (χ g ^ (ordCompl[2] (Nat.card G))) ^
    (2 ^ (Nat.card G).factorization 2) = 1
  rw [← pow_mul, Nat.mul_comm,
    Nat.ordProj_mul_ordCompl_eq_self, ← map_pow, pow_card_eq_one', map_one]

/-- Odd powers leave all involution values unchanged. -/
theorem binaryPrimaryPart_apply_of_square_eq_one (χ : G →* A)
    (z : G) (hz : z ^ 2 = 1) : binaryPrimaryPart χ z = χ z := by
  have hm : (ordCompl[2] (Nat.card G)) % 2 = 1 :=
    Nat.two_dvd_ne_zero.mp
      (Nat.not_dvd_ordCompl Nat.prime_two (Nat.card_pos (α := G)).ne')
  have hχ : (χ z) ^ 2 = 1 := by rw [← map_pow, hz, map_one]
  change (χ z) ^ (ordCompl[2] (Nat.card G)) = χ z
  rw [pow_eq_pow_mod _ hχ, hm, pow_one]

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]

/-- A full-order character of the abelianization detects any involution
outside the derived subgroup. Its binary-primary part still detects it. -/
theorem exists_binaryPrimaryLinearCharacter_detects (z : G)
    (hz : z ^ 2 = 1) (hderived : z ∉ commutator G) :
    ∃ χ : G →* kˣ, IsPGroup 2 χ.range ∧ χ z ≠ 1 := by
  have hzab : Abelianization.of z ≠ 1 := by
    intro h
    apply hderived
    rw [← Abelianization.ker_of G]
    exact h
  letI : NeZero ((Monoid.exponent (Abelianization G) : ℕ) : k) :=
    ⟨by exact_mod_cast
      (Monoid.exponent_ne_zero_of_finite (G := Abelianization G))⟩
  obtain ⟨χ, hχ⟩ :=
    CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity
      (Abelianization G) k hzab
  refine ⟨binaryPrimaryPart (χ.comp Abelianization.of),
    binaryPrimaryPart_isPGroup _, ?_⟩
  rw [binaryPrimaryPart_apply_of_square_eq_one _ z hz]
  exact hχ

/-- The obstruction to detecting an involution by a linear prefix is
exactly membership in the derived subgroup. -/
theorem exists_binaryPrimaryLinearCharacter_detects_iff (z : G)
    (hz : z ^ 2 = 1) :
    (∃ χ : G →* kˣ, IsPGroup 2 χ.range ∧ χ z ≠ 1) ↔
      z ∉ commutator G := by
  constructor
  · rintro ⟨χ, _, hχ⟩ hzderived
    exact hχ (Abelianization.commutator_subset_ker χ hzderived)
  · exact exists_binaryPrimaryLinearCharacter_detects z hz

/-- The order-four regression: the constructed character detects the
square, so its value on the original element cannot be merely a sign. -/
theorem exists_binaryPrimaryLinearCharacter_detects_square (g : G)
    (hg : g ^ 4 = 1) (hderived : g ^ 2 ∉ commutator G) :
    ∃ χ : G →* kˣ, IsPGroup 2 χ.range ∧
      (χ g) ^ 4 = 1 ∧ (χ g) ^ 2 ≠ 1 := by
  have hsquare : (g ^ 2) ^ 2 = 1 := by
    simpa only [← pow_mul] using hg
  obtain ⟨χ, hbinary, hχ⟩ :=
    exists_binaryPrimaryLinearCharacter_detects (k := k) (g ^ 2) hsquare hderived
  refine ⟨χ, hbinary, ?_, ?_⟩
  · rw [← map_pow, hg, map_one]
  · simpa only [map_pow] using hχ

/-- The actual central binary socle directions lying in a subgroup. -/
def binaryCentralOmegaSubmodule (N : Subgroup G) :
    Submodule (ZMod 2) (Additive (binaryCentralOmega G)) :=
  ((N.comap (binaryCentralOmegaEmbedding (G := G))).toAddSubgroup).toZModSubmodule 2

omit [Finite G] in
@[simp] theorem mem_binaryCentralOmegaSubmodule (N : Subgroup G)
    (z : Additive (binaryCentralOmega G)) :
    z ∈ binaryCentralOmegaSubmodule N ↔
      binaryCentralOmegaEmbedding z.toMul ∈ N := Iff.rfl

/-- Detecting one direction strictly lowers the residual central rank. -/
theorem binaryCentralOmegaSubmodule_ker_finrank_lt (χ : G →* A)
    (z : binaryCentralOmega G)
    (hχ : χ (binaryCentralOmegaEmbedding z) ≠ 1) :
    Module.finrank (ZMod 2) (binaryCentralOmegaSubmodule χ.ker) <
      Module.finrank (ZMod 2) (Additive (binaryCentralOmega G)) := by
  apply Submodule.finrank_lt
  intro htop
  have hz : Additive.ofMul z ∈ binaryCentralOmegaSubmodule χ.ker := by
    rw [htop]
    exact Submodule.mem_top
  exact hχ hz

/-- If there are at most `r + 1` central binary directions and at most
`r` of them lie in the derived subgroup, one binary-primary linear
character leaves central rank at most `r`. The character may be trivial
when the original central rank is already at most `r`. -/
theorem exists_binaryPrimaryLinearCharacter_residual_rank_le (r : ℕ)
    (hcentral : Module.finrank (ZMod 2) (Additive (binaryCentralOmega G)) ≤ r + 1)
    (hderived : Module.finrank (ZMod 2)
      (binaryCentralOmegaSubmodule (commutator G)) ≤ r) :
    ∃ χ : G →* kˣ, IsPGroup 2 χ.range ∧
      Module.finrank (ZMod 2) (binaryCentralOmegaSubmodule χ.ker) ≤ r := by
  by_cases hsmall :
      Module.finrank (ZMod 2) (Additive (binaryCentralOmega G)) ≤ r
  · let χ : G →* kˣ := binaryPrimaryPart 1
    exact ⟨χ, binaryPrimaryPart_isPGroup _,
      (Submodule.finrank_le (binaryCentralOmegaSubmodule χ.ker)).trans hsmall⟩
  · have hex : ∃ z : binaryCentralOmega G,
        binaryCentralOmegaEmbedding z ∉ commutator G := by
      by_contra h
      push Not at h
      have htop : binaryCentralOmegaSubmodule (commutator G) = ⊤ := by
        apply top_unique
        intro z _
        exact h z.toMul
      rw [htop, finrank_top] at hderived
      exact hsmall hderived
    obtain ⟨z, hz⟩ := hex
    have hzsquare : (binaryCentralOmegaEmbedding z) ^ 2 = 1 :=
      (binaryCentralOmegaEquiv G z).property.2
    obtain ⟨χ, hbinary, hχ⟩ :=
      exists_binaryPrimaryLinearCharacter_detects (k := k)
        (binaryCentralOmegaEmbedding z) hzsquare hz
    refine ⟨χ, hbinary, ?_⟩
    have hlt := binaryCentralOmegaSubmodule_ker_finrank_lt χ z hχ
    omega

end SymmetricSubgroupAsymptotics
