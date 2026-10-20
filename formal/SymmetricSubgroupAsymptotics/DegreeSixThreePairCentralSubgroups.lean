import SymmetricSubgroupAsymptotics.DegreeSixThreePairWreathChart
import Mathlib.GroupTheory.Coset.Card

/-! # Subgroups of a product with a prime binary factor

A subgroup of `K × C2` is isomorphic either to its first projection, or
to the product of that projection with `C2`. The second alternative
occurs exactly when the first projection has nontrivial kernel.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.DegreeSixThreePairCentralSubgroups

abbrev C2 := Multiplicative (ZMod 2)

theorem card_two : Nat.card C2 = 2 := by
  exact (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod 2)

/-- The chart retains the literal first-projection subgroup; no subgroup
classification is a premise. -/
def subgroupChart {K : Type} [Group K] [Finite K]
    (H : Subgroup (K × C2)) :
    Σ J : Subgroup K, (H ≃* J) ⊕ (H ≃* J × C2) := by
  let f : H →* K := (MonoidHom.fst K C2).comp H.subtype
  let s : H →* C2 := (MonoidHom.snd K C2).comp H.subtype
  by_cases hker : f.ker = ⊥
  · exact ⟨f.range, .inl (MonoidHom.ofInjective ((MonoidHom.ker_eq_bot_iff f).mp hker))⟩
  · let t : f.ker →* C2 := s.comp f.ker.subtype
    have ht : Function.Injective t := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · exact a.property.trans b.property.symm
      · exact hab
    have hdiv : Nat.card f.ker ∣ 2 := by
      simpa only [card_two] using Subgroup.card_dvd_of_injective t ht
    have hcard : Nat.card f.ker = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h | h
      · have hlo : 1 < Nat.card f.ker := f.ker.one_lt_card_iff_ne_bot.mpr hker
        omega
      · exact h
    have hts : Function.Surjective t :=
      ((Nat.bijective_iff_injective_and_card t).2
        ⟨ht, hcard.trans card_two.symm⟩).2
    let joint : H →* f.range × C2 := f.rangeRestrict.prod s
    have hji : Function.Injective joint := by
      intro a b hab
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg (fun z : f.range × C2 => (z.1 : K)) hab
      · exact congrArg (fun z : f.range × C2 => z.2) hab
    have hjs : Function.Surjective joint := by
      rintro ⟨j, c⟩
      obtain ⟨h, hh⟩ := f.rangeRestrict_surjective j
      obtain ⟨k, hk⟩ := hts ((s h)⁻¹ * c)
      refine ⟨h * (k : H), ?_⟩
      apply Prod.ext
      · apply Subtype.ext
        change f (h * (k : H)) = (j : K)
        rw [map_mul, k.property, mul_one]
        exact congrArg Subtype.val hh
      · change s (h * (k : H)) = c
        rw [map_mul]
        change s h * t k = c
        rw [hk, mul_inv_cancel_left]
    exact ⟨f.range, .inr (MulEquiv.ofBijective joint ⟨hji, hjs⟩)⟩

end SymmetricSubgroupAsymptotics.DegreeSixThreePairCentralSubgroups

end
