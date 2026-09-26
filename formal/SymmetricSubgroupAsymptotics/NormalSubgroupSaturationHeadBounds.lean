import SymmetricSubgroupAsymptotics.NormalSubgroupSaturationCommutators
import SymmetricSubgroupAsymptotics.PrimeSubdirectNormalRank

/-! A common actual relative radical makes original invariant heads
monotone by positive-cardinality cancellation. Nonempty saturation words
install that common radical outside R_D, so the maximum over every
original normal inside B is exactly max(m(R_D),d_G(B)). No monotonicity of
arbitrary subgroup generator rank or independent normal menu is assumed. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime] {G : Type*} [Group G] [Finite G]

/-- Head monotonicity here follows from equality of the actual radicals,
not from a general assertion about ranks of subgroups. -/
theorem primeRelativeHead_le_of_relativeRadical_eq
    (M B : Subgroup G) [M.Normal] [B.Normal] (hMB : M ≤ B)
    (hR : primeRelativeRadical p M = primeRelativeRadical p B) :
    Module.finrank (ZMod p) (primeRelativeCharacters p M) ≤
      Module.finrank (ZMod p) (primeRelativeCharacters p B) := by
  have hc : Nat.card M ≤ Nat.card B := Subgroup.card_le_of_le hMB
  rw [primeRelativeRadical_card_factorization p M,
    primeRelativeRadical_card_factorization p B, hR] at hc
  have hp := Nat.le_of_mul_le_mul_right hc
    (Nat.card_pos (α := primeRelativeRadical p B))
  exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hp

/-- An actual index-p cardinal relation removes exactly one head
dimension when the two original radicals are literally equal. -/
theorem primeRelativeHead_add_one_eq_of_relativeRadical_eq_and_card
    (B D : Subgroup G) [B.Normal] [D.Normal]
    (hR : primeRelativeRadical p B = primeRelativeRadical p D)
    (hcard : p * Nat.card B = Nat.card D) :
    Module.finrank (ZMod p) (primeRelativeCharacters p B) + 1 =
      Module.finrank (ZMod p) (primeRelativeCharacters p D) := by
  rw [primeRelativeRadical_card_factorization p B,
    primeRelativeRadical_card_factorization p D, hR] at hcard
  apply Nat.pow_right_injective (Fact.out : p.Prime).one_lt
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := primeRelativeRadical p D))
  simpa only [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcard

namespace NormalSubgroupSaturationCertificate

variable {ι κ : Type*} {D : Subgroup G} [D.Normal]
    {ambient : ι → G} {radicalGenerators : κ → G} {n : ℕ}
variable (C : NormalSubgroupSaturationCertificate D
  (primeRelativeRadical p D) ambient radicalGenerators n)
include C

/-- Both original radicals are the same R_D by the actual nonempty-word
certificate, so every original M≤B outside R_D has head at most that of B. -/
theorem relativeHead_le_of_not_le_radical (hne : C.NonemptyWords)
    (B : Subgroup G) [B.Normal] (hBD : B ≤ D)
    (hBnot : ¬B ≤ primeRelativeRadical p D)
    (M : Subgroup G) [M.Normal] (hMB : M ≤ B)
    (hMnot : ¬M ≤ primeRelativeRadical p D) :
    Module.finrank (ZMod p) (primeRelativeCharacters p M) ≤
      Module.finrank (ZMod p) (primeRelativeCharacters p B) := by
  apply primeRelativeHead_le_of_relativeRadical_eq p M B hMB
  exact (C.relativeRadical_eq p hne M (hMB.trans hBD) hMnot).trans
    (C.relativeRadical_eq p hne B hBD hBnot).symm

/-- This quantifies over every whole-original-group normal M inside B.
The sole bound supplied below R_D is also over every original normal. -/
theorem relativeHead_le_max (hne : C.NonemptyWords) (s : ℕ)
    (hs : ∀ (M : Subgroup G) [M.Normal], M ≤ primeRelativeRadical p D →
      Module.finrank (ZMod p) (primeRelativeCharacters p M) ≤ s)
    (B : Subgroup G) [B.Normal] (hBD : B ≤ D)
    (hBnot : ¬B ≤ primeRelativeRadical p D)
    (M : Subgroup G) [M.Normal] (hMB : M ≤ B) :
    Module.finrank (ZMod p) (primeRelativeCharacters p M) ≤
      max s (Module.finrank (ZMod p) (primeRelativeCharacters p B)) := by
  by_cases hMR : M ≤ primeRelativeRadical p D
  · exact (hs M hMR).trans (le_max_left _ _)
  · exact (C.relativeHead_le_of_not_le_radical p hne B hBD hBnot M hMB hMR).trans
      (le_max_right _ _)

theorem normalHeadMax_le_max (hne : C.NonemptyWords) (s : ℕ)
    (hs : ∀ (M : Subgroup G) [M.Normal], M ≤ primeRelativeRadical p D →
      Module.finrank (ZMod p) (primeRelativeCharacters p M) ≤ s)
    (B : Subgroup G) [B.Normal] (hBD : B ≤ D)
    (hBnot : ¬B ≤ primeRelativeRadical p D) :
    primeNormalHeadMax p B ≤
      max s (Module.finrank (ZMod p) (primeRelativeCharacters p B)) := by
  apply (primeNormalHeadMax_le_iff p B _).mpr
  intro M _ hMB
  exact C.relativeHead_le_max p hne s hs B hBD hBnot M hMB

/-- The complete maximum splits exactly at the same actual R_D. The
lower bound retains R_D≤B and the original normal B itself. -/
theorem normalHeadMax_eq_max (hne : C.NonemptyWords)
    (B : Subgroup G) [B.Normal] (hBD : B ≤ D)
    (hBnot : ¬B ≤ primeRelativeRadical p D) :
    primeNormalHeadMax p B =
      max (primeNormalHeadMax p (primeRelativeRadical p D))
        (Module.finrank (ZMod p) (primeRelativeCharacters p B)) := by
  apply le_antisymm
  · exact C.normalHeadMax_le_max p hne
      (primeNormalHeadMax p (primeRelativeRadical p D))
      (fun M _ hMR => primeRelativeHead_le_normalHeadMax p (primeRelativeRadical p D) M hMR)
      B hBD hBnot
  · have hRB : primeRelativeRadical p D ≤ B :=
      (C.comparable B hBD).resolve_left hBnot
    exact max_le (primeNormalHeadMax_mono p hRB)
      (primeRelativeHead_le_normalHeadMax p B B le_rfl)

end NormalSubgroupSaturationCertificate
end SymmetricSubgroupAsymptotics
