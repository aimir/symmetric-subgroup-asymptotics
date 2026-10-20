import SymmetricSubgroupAsymptotics.KovacsPraegerAbelianization
import Mathlib.Data.Nat.Factors

/-! The ordinary section-size consequence used in RDT's Theorem 7.
The only literature input is the existing Kovács--Praeger abelianization
bound. An arbitrary abelian section is reached through the abelianization
of its ACTUAL subgroup, rather than assumed to have a permutation action. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.AbelianSectionSize

/-- A surjective abelian quotient is a literal quotient of the source
abelianization; no extension of characters is used. -/
theorem card_le_abelianization {G A : Type} [Group G] [Finite G]
    [CommGroup A] [Finite A] (f : G →* A) (hf : Function.Surjective f) :
    Nat.card A ≤ Nat.card (Abelianization G) := by
  have hs : Function.Surjective (Abelianization.lift f) := by
    intro a
    obtain ⟨g,rfl⟩ := hf a
    exact ⟨Abelianization.of g,Abelianization.lift_apply_of f g⟩
  exact Nat.card_le_card_of_surjective _ hs

/-- Theorem 2.8's bound passes to every actual abelian section, with its
original subgroup of the same symmetric group retained. -/
theorem section_card_le (hKP : KovacsPraegerAbelianizationBound)
    {b : ℕ} (H : Subgroup (Equiv.Perm (Fin b)))
    {A : Type} [CommGroup A] [Finite A]
    (f : H →* A) (hf : Function.Surjective f) :
    (Nat.card A : ℝ) ≤ (3 : ℝ)^((b : ℝ)/3) :=
  (Nat.cast_le.mpr (card_le_abelianization f hf)).trans (hKP b H)

private theorem two_pow_length_le_prod (l : List ℕ)
    (hl : ∀ p ∈ l, 2 ≤ p) : 2^l.length ≤ l.prod := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.length_cons,List.prod_cons,pow_succ]
    have hp := hl p List.mem_cons_self
    have ht := ih (fun q hq => hl q (List.mem_cons_of_mem _ hq))
    calc
      2^l.length*2 ≤ l.prod*2 := Nat.mul_le_mul_right 2 ht
      _ ≤ p*l.prod := by
        simpa only [Nat.mul_comm] using Nat.mul_le_mul_left l.prod hp

/-- Ω is the actual number of prime factors with multiplicity. -/
def omega (n : ℕ) : ℕ := n.primeFactorsList.length

theorem two_pow_omega_le {n : ℕ} (hn : n ≠ 0) : 2^omega n ≤ n := by
  calc
    2^omega n = 2^n.primeFactorsList.length := rfl
    _ ≤ n.primeFactorsList.prod :=
      two_pow_length_le_prod _ (fun p hp => (Nat.prime_of_mem_primeFactorsList hp).two_le)
    _ = n := Nat.prod_primeFactorsList hn

/-- A deliberately coarse linear bound suffices for the fixed-cutoff
constructor. In particular this has no chosen-section or marked-count input. -/
theorem section_omega_le_twice_degree (hKP : KovacsPraegerAbelianizationBound)
    {b : ℕ} (H : Subgroup (Equiv.Perm (Fin b)))
    {A : Type} [CommGroup A] [Finite A]
    (f : H →* A) (hf : Function.Surjective f) : omega (Nat.card A) ≤ 2*b := by
  have hcard := section_card_le hKP H f hf
  have hpow : (2 : ℝ)^omega (Nat.card A) ≤ (2 : ℝ)^(2*b) := by
    calc
      (2 : ℝ)^omega (Nat.card A) ≤ (Nat.card A : ℝ) := by
        exact_mod_cast two_pow_omega_le (Nat.card_pos.ne' : Nat.card A ≠ 0)
      _ ≤ (3 : ℝ)^((b : ℝ)/3) := hcard
      _ ≤ (3 : ℝ)^(b : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by have hb := Nat.cast_nonneg (α := ℝ) b; linarith)
      _ = (3 : ℝ)^b := Real.rpow_natCast _ _
      _ ≤ (4 : ℝ)^b := by gcongr <;> norm_num
      _ = (2 : ℝ)^(2*b) := by rw [pow_mul]; norm_num
  exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ)<2)).mp hpow

end SymmetricSubgroupAsymptotics.MarkedC4.AbelianSectionSize
