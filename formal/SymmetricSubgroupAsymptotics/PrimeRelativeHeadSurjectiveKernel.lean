import SymmetricSubgroupAsymptotics.PrimeRelativeRadicalSurjectiveImage
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Linarith

/-! An actual quotient that kills only elements already in the original
relative radical preserves the whole relative head. All kernel
intersections remain literal source subgroups. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {G H : Type*} [Group G] [Finite G] [Group H]

/-- Order factorization for any actual restricted image. -/
theorem subgroup_card_eq_map_mul_kernel_intersection
    (f : G →* H) (N : Subgroup G) :
    Nat.card N = Nat.card (N.map f) * Nat.card (N ⊓ f.ker : Subgroup G) := by
  let B : Subgroup N := (N ⊓ f.ker).subgroupOf N
  have hb : Nat.card B=Nat.card (N ⊓ f.ker : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show N ⊓ f.ker ≤ N from inf_le_left)).toEquiv
  have hi : B.index=Nat.card (N.map f) := by
    change (N ⊓ f.ker).relIndex N=Nat.card (N.map f)
    rw [Subgroup.inf_relIndex_left,N.relIndex_ker]
  have hc := B.card_mul_index
  rw [hb,hi] at hc
  exact hc.symm.trans (Nat.mul_comm _ _)

/-- The quotient preserves the full character head when its actual
kernel intersection was already killed by every original character. -/
theorem primeRelativeHead_map_eq_of_kernel_inf_le_radical
    (p : ℕ) [Fact p.Prime] [Finite H]
    (f : G →* H) (hf : Function.Surjective f) (N : Subgroup G) [N.Normal]
    (hkill : N ⊓ f.ker ≤ primeRelativeRadical p N) :
    letI : (N.map f).Normal := Subgroup.Normal.map inferInstance f hf
    Module.finrank (ZMod p) (primeRelativeCharacters p (N.map f)) =
      Module.finrank (ZMod p) (primeRelativeCharacters p N) := by
  letI : (N.map f).Normal := Subgroup.Normal.map inferInstance f hf
  let R := primeRelativeRadical p N
  have he : R ⊓ f.ker=N ⊓ f.ker := by
    apply le_antisymm
    · exact inf_le_inf (primeRelativeRadical_le p N) le_rfl
    · exact le_inf hkill inf_le_right
  have hN := subgroup_card_eq_map_mul_kernel_intersection f N
  have hR := subgroup_card_eq_map_mul_kernel_intersection f R
  rw [he,primeRelativeRadical_map_surjective p f hf N] at hR
  have hs := primeRelativeRadical_card_factorization p N
  have ht := primeRelativeRadical_card_factorization p (N.map f)
  have hb : 0 < Nat.card (N ⊓ f.ker : Subgroup G) := Nat.card_pos
  have hr : 0 < Nat.card (primeRelativeRadical p (N.map f)) := Nat.card_pos
  have hh : Nat.card (N.map f) =
      p ^ Module.finrank (ZMod p) (primeRelativeCharacters p N) *
        Nat.card (primeRelativeRadical p (N.map f)) := by
    apply Nat.eq_of_mul_eq_mul_right hb
    calc
      Nat.card (N.map f)*Nat.card (N ⊓ f.ker : Subgroup G)=Nat.card N := hN.symm
      _ = _ := by rw [hs,hR]; ring
  have hp : p ^ Module.finrank (ZMod p) (primeRelativeCharacters p (N.map f)) =
      p ^ Module.finrank (ZMod p) (primeRelativeCharacters p N) := by
    apply Nat.eq_of_mul_eq_mul_right hr
    exact ht.symm.trans hh
  exact (Nat.pow_right_injective (Fact.out : p.Prime).one_lt) hp

end SymmetricSubgroupAsymptotics
