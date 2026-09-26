import SymmetricSubgroupAsymptotics.PrimeSubdirectNormalRank
import SymmetricSubgroupAsymptotics.PrimeRelativeRadicalPresentation
import Mathlib.GroupTheory.Subgroup.Center

/-! One nontrivial actual relative radical saves one binary order bit in
the maximum over all original ambient-normal subgroups. Proper subgroups
use strict cardinality; the top subgroup uses its exact radical quotient.
No enumeration, p-group premise or monotonicity of generator rank is used.
-/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics

variable {G : Type*} [Group G] [Finite G]

private theorem binaryRelativeHead_pow_le_card
    (N : Subgroup G) [N.Normal] :
    2 ^ Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) ≤ Nat.card N := by
  have hpos : 1 ≤ Nat.card (primeRelativeRadical 2 N) :=
    Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
  calc
    _ = 2 ^ Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) * 1 :=
      (Nat.mul_one _).symm
    _ ≤ 2 ^ Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) *
        Nat.card (primeRelativeRadical 2 N) := Nat.mul_le_mul_left _ hpos
    _ = Nat.card N := (primeRelativeRadical_card_factorization 2 N).symm

/-- An actual order cap and one nontrivial radical control EVERY original
normal below S. No premise already bounds their relative heads. -/
theorem binaryNormalHeadMax_le_of_card_gap
    (S : Subgroup G) [S.Normal] (r : ℕ)
    (hcard : Nat.card S ≤ 2 ^ (r+1))
    (hradical : primeRelativeRadical 2 S ≠ ⊥) :
    primeNormalHeadMax 2 S ≤ r := by
  apply (primeNormalHeadMax_le_iff 2 S r).mpr
  intro N _ hNS
  by_cases he : N = S
  · subst N
    have hradicalCard : 2 ≤ Nat.card (primeRelativeRadical 2 S) :=
      (primeRelativeRadical 2 S).one_lt_card_iff_ne_bot.mpr hradical
    have hpow : 2 ^ (Module.finrank (ZMod 2) (primeRelativeCharacters 2 S) + 1) ≤
        2 ^ (r+1) := by
      calc
        _ = 2 ^ Module.finrank (ZMod 2) (primeRelativeCharacters 2 S) * 2 :=
          pow_succ _ _
        _ ≤ 2 ^ Module.finrank (ZMod 2) (primeRelativeCharacters 2 S) *
            Nat.card (primeRelativeRadical 2 S) := Nat.mul_le_mul_left _ hradicalCard
        _ = Nat.card S := (primeRelativeRadical_card_factorization 2 S).symm
        _ ≤ _ := hcard
    have hexp := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hpow
    omega
  · have hstrict : Nat.card N < Nat.card S := by
      apply lt_of_not_ge
      intro hge
      exact he (Subgroup.eq_of_le_of_card_ge hNS hge)
    have hpow : 2 ^ Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) <
        2 ^ (r+1) :=
      (binaryRelativeHead_pow_le_card N).trans_lt (hstrict.trans_le hcard)
    by_contra hnot
    have hlarge : r+1 ≤ Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) := by
      omega
    exact (not_lt_of_ge (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hlarge)) hpow

/-- One literal mixed commutator witnesses the required nontrivial
radical; the conjugating element remains in the whole original G. -/
theorem binaryNormalHeadMax_le_of_nontrivial_commutator
    (S : Subgroup G) [S.Normal] (r : ℕ)
    (hcard : Nat.card S ≤ 2 ^ (r+1))
    (s : S) (g : G) (hcomm : ⁅(s : G),g⁆ ≠ 1) :
    primeNormalHeadMax 2 S ≤ r := by
  apply binaryNormalHeadMax_le_of_card_gap S r hcard
  intro he
  have hm := commutator_mem_primeRelativeRadical 2 S s g
  rw [he, Subgroup.mem_bot] at hm
  exact hcomm hm

/-- Noncentrality supplies a mixed commutator witness without choosing a
replacement subgroup or weakening the original ambient conjugation. -/
theorem binaryNormalHeadMax_le_of_not_le_center
    (S : Subgroup G) [S.Normal] (r : ℕ)
    (hcard : Nat.card S ≤ 2 ^ (r+1))
    (hcenter : ¬ S ≤ Subgroup.center G) :
    primeNormalHeadMax 2 S ≤ r := by
  apply binaryNormalHeadMax_le_of_card_gap S r hcard
  intro he
  apply hcenter
  intro s hs
  apply Subgroup.mem_center_iff.mpr
  intro g
  have hm := commutator_mem_primeRelativeRadical 2 S ⟨s,hs⟩ g
  rw [he, Subgroup.mem_bot] at hm
  exact (commutatorElement_eq_one_iff_mul_comm.mp hm).symm

/-- Specialize to the actual derived subgroup. This still bounds all
original G-normal subgroups inside it, rather than only G' itself. -/
theorem binaryDerivedNormalRank_le_of_card_gap (r : ℕ)
    (hcard : Nat.card (commutator G) ≤ 2 ^ (r+1))
    (hradical : primeRelativeRadical 2 (commutator G) ≠ ⊥) :
    primeDerivedNormalRank 2 G ≤ r :=
  binaryNormalHeadMax_le_of_card_gap (commutator G) r hcard hradical

theorem binaryDerivedNormalRank_le_of_nontrivial_commutator (r : ℕ)
    (hcard : Nat.card (commutator G) ≤ 2 ^ (r+1))
    (s : commutator G) (g : G) (hcomm : ⁅(s : G),g⁆ ≠ 1) :
    primeDerivedNormalRank 2 G ≤ r :=
  binaryNormalHeadMax_le_of_nontrivial_commutator (commutator G) r hcard s g hcomm

theorem binaryDerivedNormalRank_le_of_not_le_center (r : ℕ)
    (hcard : Nat.card (commutator G) ≤ 2 ^ (r+1))
    (hcenter : ¬ commutator G ≤ Subgroup.center G) :
    primeDerivedNormalRank 2 G ≤ r :=
  binaryNormalHeadMax_le_of_not_le_center (commutator G) r hcard hcenter

end SymmetricSubgroupAsymptotics
