import SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicFirstLayer
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedPositiveCardinality
import SymmetricSubgroupAsymptotics.CFSGReeFFourBinaryOuterSaving
import SymmetricSubgroupAsymptotics.SubgroupActionIntersectionTransport
import SymmetricSubgroupAsymptotics.ExactHomSubgroupCardinality

/-! Exact original intersection size and honest bounds on the SAME R.
The one middle peel gives q^10, then the proved abelianization bound
charges the derived restriction by at most two. Neither exact |R|,
Frattini rank, first-layer dimension, nor irreducibility is inferred. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicRadicalCardinalityBounds
open CFSGTitsIntrinsicFirstLayer CFSGTitsIntrinsicMiddleRadical
open CFSGReeFFourFixedPositiveCardinality CFSGReeFFourSimpleInversionBlocks
open CFSGReeFFourMiddlePositiveIntersectionNormalizer CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedAmbientHom
open CFSGReeFFourFixedBruhatCover CFSGReeFFourRelativePositiveSubgroups
open CFSGReeFFourBinaryOuterSaving CFSGOpposedSubgroupPeeling
open CFSGReeFFourMiddleDerivedFiveWord SubgroupActionIntersectionTransport

private instance fixedFinite (m : ℕ) : Finite (originalModelFixed m) :=
  Finite.of_injective (fixedAmbientHom m) (fixedAmbientHom_injective m)

private theorem involution_remainder {G : Type*} [Group G]
    (U : Subgroup G) (w : G) (hw : w^2=1) :
    remainderPart U U w=U⊓U.comap (MulAut.conj w).toMonoidHom := by
  have hi : w⁻¹=w := by
    calc
      w⁻¹=w⁻¹*(w*w) := by rw [←pow_two,hw,mul_one]
      _=w := by group
  change U⊓U.map (MulAut.conj w).toMonoidHom=_
  rw [map_eq_comap_inverse (MulAut.conj) U w,hi]

private theorem paired_middle (m : ℕ) :
    fixedPairedWord m [true]=middleFixedWeyl m := by
  apply Subtype.ext
  simpa only [if_true] using single_paired_word_val m true

theorem middle_intersection_card (m : ℕ) :
    Nat.card (middlePositiveIntersection m)=(2^(2*m+1))^10 := by
  have h := fixedPositive_card_simple_peel m true
  rw [paired_middle] at h
  have hrem : remainderPart (fixedPositive m) (fixedPositive m) (middleFixedWeyl m)=
      middlePositiveIntersection m :=
    involution_remainder (fixedPositive m) (middleFixedWeyl m) (middleWeyl_square m)
  rw [hrem,if_pos rfl] at h
  have hfactor : Nat.card (middlePositiveIntersection m)*(2^(2*m+1))^2=
      (2^(2*m+1))^12 := h.symm.trans (fixedPositive_card m)
  have hq : 0<(2^(2*m+1) : ℕ)^2 := pow_pos (pow_pos (by decide : 0<(2 : ℕ)) _) 2
  apply Nat.eq_of_mul_eq_mul_right hq
  calc
    _=(2^(2*m+1))^12 := hfactor
    _=(2^(2*m+1))^10*(2^(2*m+1))^2 := by rw [←pow_add]

private abbrev D := commutator (originalModelFixed 0)
private abbrev I := middlePositiveIntersection 0
private abbrev imageInAbelianization := I.map
  (Abelianization.of : originalModelFixed 0→*Abelianization (originalModelFixed 0))

theorem source_card_factor :
    Nat.card sourceIntersection*Nat.card imageInAbelianization=1024 := by
  let f : originalModelFixed 0→*Abelianization (originalModelFixed 0) := Abelianization.of
  have he : D.subtype.range=f.ker :=
    D.range_subtype.trans (Abelianization.ker_of (originalModelFixed 0)).symm
  have hc := ExactHomSubgroupCardinality.card_comap_mul_card_map f D.subtype
    Subtype.val_injective he I
  have hnum : (2^(2*0+1))^10=1024 := by decide
  exact hc.trans ((middle_intersection_card 0).trans hnum)

theorem radical_card_bounds : 512≤Nat.card middleRadical ∧ Nat.card middleRadical≤1024 := by
  have himg : Nat.card imageInAbelianization≤2 :=
    (Nat.card_le_card_of_injective imageInAbelianization.subtype Subtype.val_injective).trans
      abelianization_card_le_two
  have hpos : 0<Nat.card imageInAbelianization := Nat.card_pos
  have hprod := source_card_factor
  have hbound : 512≤Nat.card sourceIntersection ∧ Nat.card sourceIntersection≤1024 := by
    constructor
    · have hh := Nat.mul_le_mul_left (Nat.card sourceIntersection) himg
      rw [hprod] at hh
      omega
    · nlinarith
  have he : Nat.card middleRadical=Nat.card sourceIntersection :=
    Nat.card_congr sourceEquiv.symm.toEquiv
  rw [he]
  exact hbound

end SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicRadicalCardinalityBounds
