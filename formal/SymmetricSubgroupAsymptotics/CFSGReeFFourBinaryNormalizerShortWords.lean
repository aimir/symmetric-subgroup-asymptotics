import SymmetricSubgroupAsymptotics.CFSGReeFFourReducedPositiveIntersection
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedAmbientHom

/-! A large subgroup of the actual binary positive group cannot be
normalized by any retained short word except the identity or a simple
relative Weyl word. The same subgroup is used throughout; the two
length-two possibilities are excluded by their literal squares. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryNormalizerShortWords
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourFixedAmbientHom CFSGReeFFourShortPairedWeylMenu
open CFSGReeFFourReducedPositiveIntersection CFSGReeFFourInversionPeelingWords
open CFSGReeFFourPairedModelWords CFSGReeFFourFixedBruhatCover

private instance fixed_finite : Finite (originalModelFixed 0) :=
  Finite.of_injective (fixedAmbientHom 0) (fixedAmbientHom_injective 0)

theorem shortModelWord_three_square (m : ℕ) :
    (shortModelWord m (3 : Fin 16))^2 = shortModelWord m (7 : Fin 16) := by
  change (fixedPairedWord m [false, true])^2 =
    fixedPairedWord m ([false, true] ++ [false, true])
  rw [pow_two, fixedPairedWord_append]

theorem shortModelWord_four_square (m : ℕ) :
    (shortModelWord m (4 : Fin 16))^2 = shortModelWord m (8 : Fin 16) := by
  change (fixedPairedWord m [true, false])^2 =
    fixedPairedWord m ([true, false] ++ [true, false])
  rw [pow_two, fixedPairedWord_append]

theorem shortModelWord_not_mem_normalizer_of_weight
    (S : Subgroup (originalModelFixed 0)) (hS : S ≤ fixedPositive 0)
    (hcard : 512 ≤ Nat.card S) (i : Fin 16) (hi : 4 ≤ inversionWeight i) :
    shortModelWord 0 i ∉ Subgroup.normalizer (S : Set (originalModelFixed 0)) := by
  intro hw
  have hle : S ≤ shortPositiveIntersection 0 i := by
    intro x hx
    refine ⟨hS hx, ?_⟩
    change shortModelWord 0 i * x * (shortModelWord 0 i)⁻¹ ∈ fixedPositive 0
    exact hS ((hw x).mp hx)
  have hbound := (Subgroup.card_le_of_le hle).trans
    (shortPositiveIntersection_zero_card_le i hi)
  omega

theorem normalizing_shortModelWord_weight_lt_four
    (S : Subgroup (originalModelFixed 0)) (hS : S ≤ fixedPositive 0)
    (hcard : 512 ≤ Nat.card S) (i : Fin 16)
    (hi : shortModelWord 0 i ∈ Subgroup.normalizer (S : Set (originalModelFixed 0))) :
    inversionWeight i < 4 := by
  by_contra h
  exact shortModelWord_not_mem_normalizer_of_weight S hS hcard i (by omega) hi

private theorem weight_after_four :
    ∀ i : Fin 16, 5 ≤ i.val → 4 ≤ inversionWeight i := by
  decide +kernel

theorem normalizing_shortModelWord_index_le_two
    (S : Subgroup (originalModelFixed 0)) (hS : S ≤ fixedPositive 0)
    (hcard : 512 ≤ Nat.card S) (i : Fin 16)
    (hi : shortModelWord 0 i ∈ Subgroup.normalizer (S : Set (originalModelFixed 0))) :
    i.val ≤ 2 := by
  have hw := normalizing_shortModelWord_weight_lt_four S hS hcard i hi
  have hsmall : i.val ≤ 4 := by
    by_contra h
    have hc := weight_after_four i (by omega)
    omega
  have hne3 : i.val ≠ 3 := by
    intro h
    have he : i = (3 : Fin 16) := Fin.ext h
    subst i
    have hp := (Subgroup.normalizer (S : Set (originalModelFixed 0))).pow_mem hi 2
    rw [shortModelWord_three_square] at hp
    exact shortModelWord_not_mem_normalizer_of_weight S hS hcard (7 : Fin 16)
      (by decide +kernel) hp
  have hne4 : i.val ≠ 4 := by
    intro h
    have he : i = (4 : Fin 16) := Fin.ext h
    subst i
    have hp := (Subgroup.normalizer (S : Set (originalModelFixed 0))).pow_mem hi 2
    rw [shortModelWord_four_square] at hp
    exact shortModelWord_not_mem_normalizer_of_weight S hS hcard (8 : Fin 16)
      (by decide +kernel) hp
  omega

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryNormalizerShortWords
