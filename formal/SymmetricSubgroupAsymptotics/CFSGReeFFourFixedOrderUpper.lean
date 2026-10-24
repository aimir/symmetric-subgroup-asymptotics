import SymmetricSubgroupAsymptotics.CFSGReeFFourFinitePairedWeylMenu
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedDiagonalCardinality
import SymmetricSubgroupAsymptotics.CFSGFFourOriginalPositiveDiagramImage
import SymmetricSubgroupAsymptotics.CFSGFFourE6FixedPositiveCardinality
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedAmbientHom
import SymmetricSubgroupAsymptotics.FiniteFourFactorCoverCardinality

/-! A finite cover of the same exceptional-fixed original F4 group.
The sixteen lattice actions leave an actual fixed diagonal residual;
the literal positive subgroup embeds in the proved ambient diagram-fixed
positive group. This gives a coarse polynomial order bound, including
at field order two, without simplicity or perfectness assumptions. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFixedOrderUpper
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourFixedBruhatCover
open CFSGReeFFourFinitePairedWeylMenu CFSGReeFFourFixedWordClassification
open CFSGReeFFourPairedModelWords CFSGReeFFourFixedDiagonalCardinality
open CFSGFFourOriginalPositiveDiagramImage CFSGFFourE6FixedPositiveCardinality
open CFSGFFourOriginalMiddleWords CFSGReeFFourFixedAmbientHom

private instance fixed_finite (m : ℕ) : Finite (originalModelFixed m) :=
  Finite.of_injective (fixedAmbientHom m) (fixedAmbientHom_injective m)

def menuWord (m : ℕ) (i : MenuIndex) : originalModelFixed m :=
  fixedPairedWord m (menuPairedWord i)

theorem exists_finite_fixed_cell (m : ℕ) (g : originalModelFixed m) :
    ∃ (u : fixedPositive m) (d : fixedDiagonal m) (i : MenuIndex)
      (v : fixedPositive m), g=u.val*d.val*menuWord m i*v.val := by
  obtain ⟨u,hu,d,hd,s,v,hv,he⟩ := exists_fixed_four_factor_cell m g
  obtain ⟨i,hi⟩ := exists_paired_menu_action s
  let delta := fixedPairedWord m s * (menuWord m i)⁻¹
  have hdelta : delta ∈ fixedDiagonal m :=
    equal_action_model_residual_mem (Field m) (expandPaired s)
      (expandPaired (menuPairedWord i)) hi
  refine ⟨⟨u,hu⟩,⟨d*delta,(fixedDiagonal m).mul_mem hd hdelta⟩,
    i,⟨v,hv⟩,he.trans ?_⟩
  dsimp only [delta]
  group

theorem fixedPositive_card_le (m : ℕ) :
    Nat.card (fixedPositive m) ≤ (2^(2*m+1))^24 := by
  let f : fixedPositive m → CFSGE6GeckFixedTailCardinality.fixedPositive
      (Field m) (RingEquiv.refl (Field m)) := fun u =>
    ⟨⟨rawHom (Field m) u.val.val,u.property⟩,
      Subtype.ext (rawHom_diagram_fixed (Field m) u.val.val)⟩
  have hf : Function.Injective f := by
    intro u v he
    apply Subtype.ext
    apply Subtype.ext
    exact rawHom_injective (Field m)
      (congrArg (fun z : CFSGE6GeckFixedTailCardinality.fixedPositive
        (Field m) (RingEquiv.refl (Field m)) => z.val.val) he)
  have hc := (Nat.card_le_card_of_injective f hf).trans
    (CFSGFFourE6FixedPositiveCardinality.fixedPositive_card_le
      (Field m) (RingEquiv.refl (Field m)))
  simpa only [field_card] using hc

theorem fixed_order_le (m : ℕ) :
    Nat.card (originalModelFixed m) ≤ (2^(2*m+1))^54 := by
  let q := 2^(2*m+1)
  have hq : 2 ≤ q := by
    dsimp only [q]
    exact (by decide : 2 ≤ 2^1).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hU : Nat.card (fixedPositive m) ≤ q^24 := fixedPositive_card_le m
  have hD : Nat.card (fixedDiagonal m) ≤ q^2 := by
    rw [fixedDiagonal_card]
    exact Nat.pow_le_pow_left (Nat.sub_le _ _) _
  have hcover := FiniteFourFactorCoverCardinality.card_le_of_cover
    (fixedPositive m) (fixedDiagonal m) (fixedPositive m) (menuWord m)
    (exists_finite_fixed_cell m)
  have hsmall : 16 ≤ q^4 := (by decide : 16 ≤ 2^4).trans
    (Nat.pow_le_pow_left hq _)
  calc
    Nat.card (originalModelFixed m) ≤ q^24*q^2*16*q^24 :=
      hcover.trans (Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.mul_le_mul hU hD) (le_of_eq menuIndex_card)) hU)
    _ = 16*q^50 := by ring
    _ ≤ q^4*q^50 := Nat.mul_le_mul_right _ hsmall
    _ = q^54 := by rw [← pow_add]

theorem original_ree_order_le (m : ℕ) :
    Nat.card (CFSG.Models.ReeF4 m) ≤ (2^(2*m+1))^54 := by
  rw [Nat.card_congr (originalReeEquiv m).toEquiv]
  have hq := Nat.card_le_card_of_surjective
    (QuotientGroup.mk' (Subgroup.center (commutator (originalModelFixed m))))
    (QuotientGroup.mk'_surjective _)
  exact (hq.trans (Nat.card_le_card_of_injective
    (commutator (originalModelFixed m)).subtype Subtype.val_injective)).trans
      (fixed_order_le m)

end SymmetricSubgroupAsymptotics.CFSGReeFFourFixedOrderUpper
