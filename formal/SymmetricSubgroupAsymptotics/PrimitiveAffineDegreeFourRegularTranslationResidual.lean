import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourRegularTranslationSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineProfileParity

/-!
# Elimination of the regular degree-four residual

The order-four local component left by the numerical split cannot occur.
Indeed, the regular translation subgroup already has order four, so an
order-four component has trivial point stabilizer.  A trivial stabilizer in
a primitive action of composite degree is impossible: primitivity makes the
stabilizer maximal, while Cauchy's theorem supplies a subgroup of order two.

This closes all four residual block counts `2, 4, 8, 16` without a new
capacity estimate or a finite action catalogue.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

namespace PrimitiveAffineProfile

variable {L Omega : Type} [Group L] [Finite L] [MulAction L Omega]
  [Finite Omega]

/-- A primitive regular affine profile of composite degree has nontrivial
point stabilizer.  This is the group-native form of the existing retained
action lemma, and applies in particular to a primitive block component. -/
theorem complement_nontrivial_of_proper_prime_card_divisor
    (P : PrimitiveAffineProfile L Omega)
    (hprimitive : MulAction.IsPreprimitive L Omega)
    (x : Omega) {q : ℕ} (hq : q.Prime)
    (hqdiv : q ∣ Nat.card Omega) (hqlt : q < Nat.card Omega) :
    Nontrivial (P.complement x) := by
  by_contra hnt
  have hsub : Subsingleton (P.complement x) :=
    not_nontrivial_iff_subsingleton.mp hnt
  letI : Subsingleton (P.complement x) := hsub
  have hcomp : Nat.card (P.complement x) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
  have hV : Nat.card P.V = Nat.card Omega := P.card_eq x
  have hL : Nat.card L = Nat.card Omega := by
    calc
      Nat.card L = Nat.card P.V * Nat.card (P.complement x) :=
        (P.isComplement'_complement x).card_mul.symm
      _ = Nat.card Omega := by rw [hV, hcomp, mul_one]
  letI : Fact q.Prime := ⟨hq⟩
  obtain ⟨K, hKcard⟩ :=
    Sylow.exists_subgroup_card_pow_prime (G := L) q (n := 1)
      (by rw [pow_one, hL]; exact hqdiv)
  have hKcard' : Nat.card K = q := by simpa using hKcard
  have hKne : K ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hKcard'
    exact hq.one_lt.ne' hKcard'.symm
  have hstabilizer : P.complement x = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    exact congrArg Subtype.val
      (Subsingleton.elim (⟨g, hg⟩ : P.complement x) 1)
  have hOmega2 : 2 ≤ Nat.card Omega :=
    hq.two_le.trans (Nat.le_of_lt hqlt)
  letI : Nontrivial Omega :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  letI : MulAction.IsPreprimitive L Omega := hprimitive
  have hcoat : IsCoatom (P.complement x) :=
    MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive x
  rw [hstabilizer] at hcoat
  have hKtop : K = ⊤ :=
    (hcoat.ne_iff_eq_top bot_le).mp hKne
  have hcardTop : Nat.card K = Nat.card Omega := by
    rw [hKtop, Subgroup.card_top, hL]
  have : q = Nat.card Omega := hKcard'.symm.trans hcardTop
  exact (Nat.ne_of_lt hqlt) this

end PrimitiveAffineProfile

namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)

/-- A primitive affine component of degree four cannot consist only of its
regular translation subgroup. -/
theorem degreeFour_component_card_ne_four
    (hr : Nat.card block.Fibre = 4) :
    Nat.card block.Component ≠ 4 := by
  intro hcomponent
  let x : block.Fibre := origin block
  have hcompNt : Nontrivial (P.complement x) :=
    P.complement_nontrivial_of_proper_prime_card_divisor
      block.component_preprimitive x Nat.prime_two
      (by rw [hr]; norm_num) (by rw [hr]; norm_num)
  have hcompTwo : 2 ≤ Nat.card (P.complement x) :=
    Finite.one_lt_card_iff_nontrivial.mpr hcompNt
  have hV : Nat.card P.V = 4 := (P.card_eq x).trans hr
  have hfactor := (P.isComplement'_complement x).card_mul
  rw [hV, hcomponent] at hfactor
  omega

/-- The purported order-four component yields a source at every block
count, hence in particular on the exact residual `2, 4, 8, 16`. -/
noncomputable def degreeFourRegularTranslationSource_of_component_card_four
    (hr : Nat.card block.Fibre = 4)
    (hcomponent : Nat.card block.Component = 4) :
    PreE7RankTailSourceOrYonedaTopData w U :=
  False.elim ((degreeFour_component_card_ne_four block P hr) hcomponent)

/-- Named wrapper for the residual returned by
`degreeFourRegularTranslationExceptionalExhaustion`. -/
noncomputable def degreeFourRegularTranslationResidualSource
    (hr : Nat.card block.Fibre = 4)
    (hcomponent : Nat.card block.Component = 4)
    (_hs : IsDegreeFourRegularTranslationResidualBlockCount
      (Nat.card block.Points)) :
    PreE7RankTailSourceOrYonedaTopData w U :=
  degreeFourRegularTranslationSource_of_component_card_four block P
    hr hcomponent

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
