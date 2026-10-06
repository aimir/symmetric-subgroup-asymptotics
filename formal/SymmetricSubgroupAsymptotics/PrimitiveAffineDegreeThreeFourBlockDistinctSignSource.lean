import SymmetricSubgroupAsymptotics.MinimalSelfCentralizingCompleteQuotient
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockDistinctSignDerivedTarget
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoQuotientEnvelopeTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixTailSource
import SymmetricSubgroupAsymptotics.Non2PreE7S3ExceptionalEnvelope

/-!
# The four-distinct-sign S3EXC source

In the four-sign branch the correlated ternary translation layer is the
full four-coordinate module.  It is minimal and self-centralizing, so every
nonbottom normal axis contains it and enters the complete normal menu of the
literal signed degree-eight quotient.  The bottom axis is the original
nonsplit ternary cyclic-dual target.

Thus the complete, correlated estimate is

`Z_J(U) <= Z_J(U/E) + |Aut U| 2^((log_2 3 / 3)b)`.

The quotient is transported to its actual four-pair action only after this
joint all-normal estimate is proved.  The finite automorphism coefficient is
paid from the actual extension order: `|E| = 3^4`, while `U/E` embeds in
`S_8`.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- Four independent ternary translation coordinates give an elementary
normal subgroup of order `3^4`. -/
theorem degreeThreeFourBlock_translationIntersection_card
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (hfour :
      (degreeThreeFourBlockSignedIsotypeProfile
        block P hr hs hcomponent).isotypeCount = 4) :
    Nat.card (E block P) = 81 := by
  letI : Fact P.p.Prime := (chart block P).primeFact
  letI : Finite (chart block P).V :=
    Module.finite_of_finite (ZMod P.p)
  let coordinates := degreeThreeFourBlockTranslationCoordinateEquiv
    block P hr hs hcomponent hbinary hfour
  have hlocal : Nat.card (chart block P).V = 3 := by
    calc
      Nat.card (chart block P).V =
          Nat.card (Multiplicative (chart block P).V) := rfl
      _ = Nat.card P.V :=
        Nat.card_congr (chart block P).equiv.symm.toEquiv
      _ = Nat.card block.Fibre := P.card_eq (origin block)
      _ = 3 := hr
  calc
    Nat.card (E block P) =
        Nat.card (Multiplicative (TranslationSubmodule block P)) :=
      Nat.card_congr (translationMulEquiv block P).toEquiv
    _ = Nat.card (TranslationSubmodule block P) := rfl
    _ = Nat.card (Fin 4 → (chart block P).V) :=
      Nat.card_congr coordinates.toEquiv
    _ = Nat.card (chart block P).V ^ Nat.card (Fin 4) := Nat.card_fun
    _ = 3 ^ 4 := by rw [hlocal, Nat.card_fin]
    _ = 81 := by norm_num

/-- The literal signed quotient has order at most `2^16`, simply because
its retained four-pair action embeds in `S_8`. -/
theorem degreeThreeFourBlock_signedQuotient_card_le
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6) :
    Nat.card (preE7NonPairAction w U ⧸ E block P) ≤ 2 ^ 16 := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  calc
    Nat.card (preE7NonPairAction w U ⧸ E block P) = Nat.card C.action :=
      Nat.card_congr C.sourceEquiv.toEquiv
    _ ≤ Nat.card (Equiv.Perm (Fin (2 * 4))) :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    _ = Nat.factorial (2 * 4) := by rw [Nat.card_perm, Nat.card_fin]
    _ ≤ 2 ^ 16 := by norm_num

/-- The original degree-twelve action has order at most `2^24`.  This
deliberately uses only the literal extension and the faithful degree-eight
quotient action; no finite action catalogue is invoked. -/
theorem degreeThreeFourBlock_distinctSign_order_le
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (hfour :
      (degreeThreeFourBlockSignedIsotypeProfile
        block P hr hs hcomponent).isotypeCount = 4) :
    Nat.card (preE7NonPairAction w U) ≤ 2 ^ 24 := by
  have hfactor :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (E block P)
  have hE : Nat.card (E block P) ≤ 2 ^ 8 := by
    rw [degreeThreeFourBlock_translationIntersection_card
      block P hr hs hcomponent hbinary hfour]
    norm_num
  have hQ := degreeThreeFourBlock_signedQuotient_card_le
    block P hr hs hcomponent
  calc
    Nat.card (preE7NonPairAction w U) =
        Nat.card (preE7NonPairAction w U ⧸ E block P) *
          Nat.card (E block P) := hfactor
    _ ≤ (2 ^ 16) * (2 ^ 8) := Nat.mul_le_mul hQ hE
    _ = 2 ^ 24 := by norm_num

/-- The automorphism coefficient of the bottom cyclic-dual row fits the
uniform logarithmic-square menu. -/
theorem degreeThreeFourBlock_distinctSign_aut_le_menu
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (hfour :
      (degreeThreeFourBlockSignedIsotypeProfile
        block P hr hs hcomponent).isotypeCount = 4)
    (b : ℕ) :
    (Nat.card (preE7NonPairAction w U ≃*
        preE7NonPairAction w U) : ℝ) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2) := by
  have hw : w = 12 := by
    calc
      w = Nat.card block.Fibre * Nat.card block.Points := width_eq block
      _ = 3 * 4 := by rw [hr, hs]
      _ = 12 := by norm_num
  have horder := degreeThreeFourBlock_distinctSign_order_le
    block P hr hs hcomponent hbinary hfour
  have haut := mulEquiv_card_le_two_pow_sq_of_order 24 horder
  have hcast :
      (Nat.card (preE7NonPairAction w U ≃*
          preE7NonPairAction w U) : ℝ) ≤
        (2 : ℝ) ^ (24 * 24 : ℕ) := by
    exact_mod_cast haut
  calc
    (Nat.card (preE7NonPairAction w U ≃*
        preE7NonPairAction w U) : ℝ) ≤
        (2 : ℝ) ^ (24 * 24 : ℕ) := hcast
    _ = (2 : ℝ) ^ ((24 * 24 : ℕ) : ℝ) :=
      (Real.rpow_natCast _ _).symm
    _ ≤ (2 : ℝ) ^ (64 * (w : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      rw [hw]
      norm_num
    _ ≤ _ := two_rpow_sixtyFour_width_le_menuMass
      (hw.symm ▸ (by norm_num : 8 ≤ 12)) b

/-- The exact complete all-normal estimate in the four-sign branch. -/
theorem degreeThreeFourBlock_distinctSign_completeWeight
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (hfour :
      (degreeThreeFourBlockSignedIsotypeProfile
        block P hr hs hcomponent).isotypeCount = 4)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := preE7NonPairAction w U) J ≤
      completeQuotientWeight
          (R := (degreeThreeFourBlockPairChart
            block P hr hs hcomponent).action) J +
        (Nat.card (preE7NonPairAction w U ≃*
            preE7NonPairAction w U) : ℝ) *
          (2 : ℝ) ^ ((Real.logb 2 3 / 3) * b) := by
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  have hmin := degreeThreeFourBlock_translationIntersection_minimal
    block P hr hs hcomponent hbinary hfour
  have hself := degreeThreeFourBlock_translationIntersection_selfCentralizing
    block P hr hs hcomponent hbinary hfour
  have hnormal := completeQuotientWeight_le_quotient_add_epimorphism
    (E block P) hmin hself J
  have hp : P.p = 3 := (degreeThree_translation_prime_dim block P hr).1
  let T := degreeThreeFourBlock_distinctSignDerivedCyclicTarget
    block P hr hs hcomponent hbinary hfour
  have T3 : DerivedHead.DerivedCyclicTarget
      (preE7NonPairAction w U) (E block P)
      (degreeThreeFourBlock_signedQuotientDerivedLength
        block P hr hs hcomponent hbinary).t 3 := by
    simpa only [hp] using T
  have htail := T3.epi_card_le_ternary J
  calc
    completeQuotientWeight (R := preE7NonPairAction w U) J ≤
        completeQuotientWeight
            (R := preE7NonPairAction w U ⧸ E block P) J +
          (Nat.card (GroupEpimorphism J
            (preE7NonPairAction w U)) : ℝ) := hnormal
    _ ≤ completeQuotientWeight
            (R := preE7NonPairAction w U ⧸ E block P) J +
          (Nat.card (preE7NonPairAction w U ≃*
              preE7NonPairAction w U) : ℝ) *
            (2 : ℝ) ^ ((Real.logb 2 3 / 3) * b) :=
      add_le_add_right htail _
    _ = _ := by
      rw [completeQuotientWeight_congr C.sourceEquiv J]

/-- Concrete S3EXC source for the four-distinct-sign residual action. -/
noncomputable def degreeThreeFourBlock_distinctSignExceptionalSource
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (hfour :
      (degreeThreeFourBlockSignedIsotypeProfile
        block P hr hs hcomponent).isotypeCount = 4) :
    PreE7S3ExceptionalSource w U where
  sourceDegree := 8
  sourceDegree_two := by norm_num
  Q := (degreeThreeFourBlockPairChart block P hr hs hcomponent).action
  B := 1
  C := Nat.card (preE7NonPairAction w U ≃* preE7NonPairAction w U)
  eta := 0
  theta := Real.logb 2 3 / 3
  B_nonneg := zero_le_one
  C_nonneg := Nat.cast_nonneg _
  eta_nonneg := le_rfl
  exponent_margin := by
    have hw : w = 12 := by
      calc
        w = Nat.card block.Fibre * Nat.card block.Points := width_eq block
        _ = 3 * 4 := by rw [hr, hs]
        _ = 12 := by norm_num
    rw [hw]
    norm_num [preE7CharacterRho, evenWidth, halfDegree]
  tail_window := logThreeThird_le_window (by
    have hw : w = 12 := by
      calc
        w = Nat.card block.Fibre * Nat.card block.Points := width_eq block
        _ = 3 * 4 := by rw [hr, hs]
        _ = 12 := by norm_num
    omega)
  complete_bound := by
    intro b J
    simpa only [zero_mul, Real.rpow_zero, mul_one, one_mul] using
      degreeThreeFourBlock_distinctSign_completeWeight
        block P hr hs hcomponent hbinary hfour J
  main_menu := fun b ↦ by
    exact Real.one_le_rpow (by norm_num) (by positivity)
  tail_menu := degreeThreeFourBlock_distinctSign_aut_le_menu
    block P hr hs hcomponent hbinary hfour

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
