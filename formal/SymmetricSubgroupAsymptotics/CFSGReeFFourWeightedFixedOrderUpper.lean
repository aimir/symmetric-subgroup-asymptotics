import SymmetricSubgroupAsymptotics.CFSGReeFFourShortMenuPeeling
import SymmetricSubgroupAsymptotics.CFSGOpposedSubgroupPeelingCover
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleTorusSquareReduction

/-! The weighted sixteen-cell cover of the original exceptional-fixed
group. Actual opposed residuals absorb the right factor, so its cost
is the proved inversion weight rather than a second copy of all U.
The order ceiling descends to the original derived/full-centre model;
no simplicity, perfectness or Tits identification is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourWeightedFixedOrderUpper
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourFixedBruhatCover CFSGReeFFourFixedAmbientHom
open CFSGReeFFourFieldParameters CFSGTwistedE6GeckNormalizerEnvelope
open CFSGReeFFourShortPairedWeylMenu CFSGReeFFourShortMenuPeeling
open CFSGReeFFourFixedDiagonalCardinality CFSGOpposedSubgroupPeelingCover

private instance fixed_finite (m : ℕ) : Finite (originalModelFixed m) :=
  Finite.of_injective (fixedAmbientHom m) (fixedAmbientHom_injective m)

theorem fixed_order_le (m : ℕ) :
    Nat.card (originalModelFixed m) ≤ (2^(2*m+1))^26 := by
  have hD (d : fixedDiagonal m) (u : fixedPositive m) :
      d.val*u.val*d.val⁻¹ ∈ fixedPositive m := by
    have hraw : fixedRawHom m d.val ∈ diagonalNormalizer (Field m) := d.property
    have hn : d.val ∈ Subgroup.normalizer
        (fixedPositive m : Set (originalModelFixed m)) :=
      Subgroup.le_normalizer_comap (fixedRawHom m) hraw.1.1
    exact (Subgroup.mem_normalizer_iff.mp hn u.val).mp u.property
  have hR (i : Fin 16) (r : originalModelFixed m) (hr : r ∈ shortResidual m i) :
      shortModelWord m i*r*(shortModelWord m i)⁻¹ ∈ fixedPositive m := by
    obtain ⟨u,hu,he⟩ := shortResidual_le_conjugate m i hr
    change (shortModelWord m i)⁻¹*u*((shortModelWord m i)⁻¹)⁻¹=r at he
    have hx : shortModelWord m i*r*(shortModelWord m i)⁻¹=u := by rw [←he]; group
    rw [hx]
    exact hu
  have h := card_le_ambient_residual_cover (fixedPositive m) (fixedDiagonal m)
    (shortModelWord m) (shortResidual m)
    (fun i => (2^(2*m+1))^(inversionWeight i))
    (shortResidual_le m) (exists_short_fixed_cell m) hD hR
    (shortResidual_card_factorization m)
  rw [CFSGReeFFourFixedPositiveCardinality.fixedPositive_card,
    fixedDiagonal_card,weighted_short_menu] at h
  have hq : 2 ≤ 2^(2*m+1) :=
    (by decide : 2 ≤ (2 : ℕ)^1).trans (Nat.pow_le_pow_right (by decide) (by omega))
  exact h.trans (CFSGReeFFourWeightedBruhatNumerics.positive_torus_weightedMenu_le _ hq)

theorem original_ree_order_le (m : ℕ) :
    Nat.card (CFSG.Models.ReeF4 m) ≤ (2^(2*m+1))^26 := by
  rw [Nat.card_congr (originalReeEquiv m).toEquiv]
  have hq := Nat.card_le_card_of_surjective
    (QuotientGroup.mk' (Subgroup.center (commutator (originalModelFixed m))))
    (QuotientGroup.mk'_surjective _)
  exact (hq.trans (Nat.card_le_card_of_injective
    (commutator (originalModelFixed m)).subtype Subtype.val_injective)).trans
      (fixed_order_le m)

end SymmetricSubgroupAsymptotics.CFSGReeFFourWeightedFixedOrderUpper
