import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignCentralSeries
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockDistinctSignDerivedTarget
import SymmetricSubgroupAsymptotics.PrimitiveAffineBlockCoordinateSeparation
import SymmetricSubgroupAsymptotics.BinaryResidualCyclicDualEpi
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixTailSource

/-!
# The full-translation cyclic-dual tail in the four-block binary branch

The two-sign proof has one genuinely non-comparator row: when the retained
ternary translation layer has dimension four, the original degree-twelve
group is a ternary cyclic-dual target.  This file constructs that row from
the literal affine coordinates.

The separating character is one actual block coordinate, transported to
`C3`.  Its ambient conjugates separate the whole correlated translation
intersection by the original-block evaluation theorem.  Full dimension
turns the injective four-coordinate map into an equivalence, which makes the
quotient conjugation action faithful and the translation layer
self-centralizing.  The binary residual theorem then gives the sharp
`3^(b/3)` tail without requiring irreducibility or minimal normality.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

private abbrev C3 := Multiplicative (ZMod 3)

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- The local translation group has order three, hence has a canonical
chosen multiplicative equivalence with `C3`. -/
noncomputable def degreeThreeLocalTranslationCyclicEquiv
    (hr : Nat.card block.Fibre = 3) :
    Multiplicative (chart block P).V ≃* C3 := by
  have hlocal : Nat.card (Multiplicative (chart block P).V) = 3 := by
    calc
      Nat.card (Multiplicative (chart block P).V) = Nat.card P.V :=
        Nat.card_congr (chart block P).equiv.symm.toEquiv
      _ = Nat.card block.Fibre := P.card_eq (origin block)
      _ = 3 := hr
  have hC3 : Nat.card C3 = 3 := by simp [C3]
  exact mulEquivOfPrimeCardEq hlocal hC3

/-- One actual translation coordinate, written as a ternary cyclic
character. -/
noncomputable def degreeThreeFourBlockTranslationCharacter
    (hr : Nat.card block.Fibre = 3) :
    E block P →* C3 :=
  (degreeThreeLocalTranslationCyclicEquiv block P hr).toMonoidHom.comp
    (coordinate block P block.base)

/-- Ambient conjugates of the selected coordinate character separate the
whole literal translation intersection. -/
theorem degreeThreeFourBlockTranslationCharacter_separating
    (hr : Nat.card block.Fibre = 3)
    (a : E block P)
    (ha : ∀ g : preE7NonPairAction w U,
      degreeThreeFourBlockTranslationCharacter block P hr
        (MulAut.conjNormal g a) = 1) :
    a = 1 := by
  apply translationCoordinate_conjugates_separate block P a
  intro g
  let e := degreeThreeLocalTranslationCyclicEquiv block P hr
  apply e.injective
  have hg := ha g
  change e (coordinate block P block.base (MulAut.conjNormal g a)) = 1 at hg
  rw [hg, map_one]

/-- The actual translation intersection is a ternary group; correlations
between its four coordinates are retained. -/
theorem degreeThreeFourBlock_translationIntersection_isPGroup
    (hr : Nat.card block.Fibre = 3) :
    IsPGroup 3 (E block P) := by
  letI : Fact P.p.Prime := (chart block P).primeFact
  have hp : P.p = 3 := (degreeThree_translation_prime_dim block P hr).1
  have hmodule :
      IsPGroup P.p (Multiplicative (TranslationSubmodule block P)) :=
    ZModModule.isPGroup_multiplicative
  have hE : IsPGroup P.p (E block P) :=
    hmodule.of_equiv (translationMulEquiv block P).symm
  simpa only [hp] using hE

/-- If the correlated ternary layer has dimension four, its literal
coordinate inclusion is an equivalence with all four local coordinates. -/
noncomputable def degreeThreeFourBlockTranslationCoordinateEquiv_of_finrank_four
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hfull : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 4) :
    TranslationSubmodule block P ≃ₗ[ZMod P.p]
      (Fin 4 → (chart block P).V) := by
  let f := degreeThreeFourBlockTranslationCoordinateMap block P hs
  have hdim : Module.finrank (ZMod P.p) (chart block P).V = 1 := by
    have hdim' := (degreeThree_translation_prime_dim block P hr).2
    change Module.finrank (ZMod P.p) (chart block P).V = 1 at hdim'
    exact hdim'
  apply LinearEquiv.ofInjectiveOfFinrankEq f
    (degreeThreeFourBlockTranslationCoordinateMap_injective block P hs)
  simpa only [Module.finrank_pi, Fintype.card_fin, hdim, Nat.mul_one]
    using hfull

private theorem degreeThreeFourBlockTranslationCoordinateEquiv_of_finrank_four_apply
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hfull : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 4)
    (x : TranslationSubmodule block P) (i : Fin 4) :
    degreeThreeFourBlockTranslationCoordinateEquiv_of_finrank_four
        block P hr hs hfull x i =
      x.1 ((degreeThreeFourBlockIndexEquiv block hs).symm i) :=
  rfl

/-- Full translation dimension makes the actual quotient conjugation
representation faithful.  This is the dimension-form version of the
four-distinct-sign faithfulness theorem and does not require a sign-count
hypothesis. -/
theorem degreeThreeFourBlock_quotientRepresentation_injective_of_finrank_four
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hfull : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 4) :
    Function.Injective
      (elementaryChart block P).quotientRepresentation.ρ := by
  let e := degreeThreeFourBlockIndexEquiv block hs
  let coordinates :=
    degreeThreeFourBlockTranslationCoordinateEquiv_of_finrank_four
      block P hr hs hfull
  rw [injective_iff_map_eq_one]
  intro q hq
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (E block P) q
  have hfix : ∀ x : TranslationSubmodule block P,
      (elementaryChart block P).quotientRepresentation.ρ
        (QuotientGroup.mk' (E block P) a) x = x := by
    intro x
    have hx := DFunLike.congr_fun hq x
    simpa only [one_apply] using hx
  have hdim : Module.finrank (ZMod P.p) (chart block P).V = 1 := by
    have hdim' := (degreeThree_translation_prime_dim block P hr).2
    change Module.finrank (ZMod P.p) (chart block P).V = 1 at hdim'
    exact hdim'
  letI : Fact P.p.Prime := (chart block P).primeFact
  letI : Nontrivial (chart block P).V :=
    Module.nontrivial_of_finrank_pos (R := ZMod P.p) (by
      rw [hdim]
      decide)
  obtain ⟨z, hz⟩ := exists_ne (0 : (chart block P).V)
  have htop : (ambientEmbedding block a).right = 1 := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    by_contra hi
    let y : Fin 4 → (chart block P).V :=
      fun j ↦ if j = e i then z else 0
    let x : TranslationSubmodule block P := coordinates.symm y
    have hcoordinates : coordinates x = y := coordinates.apply_symm_apply y
    have hxi : x.1 i ≠ 0 := by
      have hvalue : x.1 i = z := by
        have h := congrFun hcoordinates (e i)
        rw [degreeThreeFourBlockTranslationCoordinateEquiv_of_finrank_four_apply,
          e.symm_apply_apply] at h
        simpa only [y, if_pos rfl] using h
      rw [hvalue]
      exact hz
    have htarget := translationSubmodule_coordinate_ne_zero_of_transport
      block P a x i hxi
    rw [hfix x] at htarget
    have hvalue := congrFun hcoordinates
      (e ((ambientEmbedding block a).right • i))
    rw [degreeThreeFourBlockTranslationCoordinateEquiv_of_finrank_four_apply,
      e.symm_apply_apply] at hvalue
    have hoff : e ((ambientEmbedding block a).right • i) ≠ e i :=
      fun h ↦ hi (e.injective h)
    have hzero : x.1 ((ambientEmbedding block a).right • i) = 0 := by
      rw [hvalue]
      simp only [y, if_neg hoff]
    exact htarget hzero
  have hlocal : ∀ i : block.Points,
      localMap block P ((ambientEmbedding block a).left i) = 1 := by
    intro i
    apply binaryAffineLocalLinearRepresentation_injective block P
    apply LinearMap.ext
    intro v
    let y : Fin 4 → (chart block P).V :=
      fun j ↦ if j = e i then v else 0
    let x : TranslationSubmodule block P := coordinates.symm y
    have hcoordinates : coordinates x = y := coordinates.apply_symm_apply y
    have hxi : x.1 i = v := by
      have hvalue := congrFun hcoordinates (e i)
      rw [degreeThreeFourBlockTranslationCoordinateEquiv_of_finrank_four_apply,
        e.symm_apply_apply] at hvalue
      simpa only [y, if_pos rfl] using hvalue
    have hcoordinate :=
      translationSubmodule_quotientRepresentation_coordinate
        block P a htop x i
    rw [hfix x, hxi] at hcoordinate
    simpa only [map_one, one_apply] using hcoordinate.symm
  apply quotientEmbedding_injective block P
  rw [quotientEmbedding,
    PermutationalWreathProduct.Compression.quotientEmbedding]
  simp only [map_one]
  change PermutationalWreathProduct.Compression.map
      (ambientEmbedding block) (localMap block P) a = 1
  apply PermutationalWreathProduct.ext
  · funext i
    change localMap block P ((ambientEmbedding block a).left i) = 1
    exact hlocal i
  · change (ambientEmbedding block a).right = 1
    exact htop

/-- The full-dimensional ternary layer is self-centralizing in the original
degree-twelve group. -/
theorem degreeThreeFourBlock_translationIntersection_selfCentralizing_of_finrank_four
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hfull : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 4) :
    ∀ g : preE7NonPairAction w U,
      (∀ e ∈ E block P, g * e = e * g) → g ∈ E block P :=
  ElementaryMinimalNormalChart.selfCentralizing_of_quotientRepresentation_injective
    (elementaryChart block P)
    (degreeThreeFourBlock_quotientRepresentation_injective_of_finrank_four
      block P hr hs hcomponent hfull)

/-- Full ternary dimension and a binary signed quotient make the original
group a binary-residual cyclic-dual target. -/
noncomputable def degreeThreeFourBlock_fullTranslationBinaryResidualTarget
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (hfull : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 4) :
    DerivedHead.BinaryResidualCyclicTarget
      (preE7NonPairAction w U) (E block P) :=
  DerivedHead.BinaryResidualCyclicTarget.of_ternary_normal_binary_quotient
    (degreeThreeFourBlock_translationIntersection_isPGroup block P hr)
    (degreeThreeFourBlock_signedQuotient_isPGroup
      block P hr hs hcomponent hbinary)
    (degreeThreeFourBlockTranslationCharacter block P hr)
    (degreeThreeFourBlock_translationIntersection_selfCentralizing_of_finrank_four
      block P hr hs hcomponent hfull)
    (degreeThreeFourBlockTranslationCharacter_separating block P hr)

/-- The sharp cyclic-dual bottom row for the full-dimensional two-sign
branch. -/
theorem degreeThreeFourBlock_fullTranslation_tail
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (hfull : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 4)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J (preE7NonPairAction w U)) : ℝ) ≤
      (Nat.card (preE7NonPairAction w U ≃*
          preE7NonPairAction w U) : ℝ) *
        (2 : ℝ) ^ ((Real.logb 2 3 / 3) * b) :=
  (degreeThreeFourBlock_fullTranslationBinaryResidualTarget
    block P hr hs hcomponent hbinary hfull).epi_card_le_ternary J

/-- A four-dimensional ternary translation intersection has order `81`. -/
theorem degreeThreeFourBlock_translationIntersection_card_of_finrank_four
    (hr : Nat.card block.Fibre = 3)
    (hfull : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 4) :
    Nat.card (E block P) = 81 := by
  letI : Fact P.p.Prime := (chart block P).primeFact
  have hp : P.p = 3 := (degreeThree_translation_prime_dim block P hr).1
  calc
    Nat.card (E block P) =
        Nat.card (Multiplicative (TranslationSubmodule block P)) :=
      Nat.card_congr (translationMulEquiv block P).toEquiv
    _ = Nat.card (TranslationSubmodule block P) := rfl
    _ = Nat.card (ZMod P.p) ^
        Module.finrank (ZMod P.p) (TranslationSubmodule block P) :=
      Module.natCard_eq_pow_finrank (K := ZMod P.p)
        (V := TranslationSubmodule block P)
    _ = 3 ^ 4 := by rw [Nat.card_zmod, hp, hfull]
    _ = 81 := by norm_num

/-- In the full-dimensional two-sign branch the original group has order
at most `2^12`. -/
theorem degreeThreeFourBlock_twoSign_fullTranslation_order_le
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (hfull : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 4) :
    Nat.card (preE7NonPairAction w U) ≤ 2 ^ 12 := by
  have hE := degreeThreeFourBlock_translationIntersection_card_of_finrank_four
    block P hr hfull
  have hquot := degreeThreeFourBlockTwoSign_signedQuotient_card_cases
    block P hr hs hcomponent hbinary htwo
  have hfactor :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (E block P)
  rw [hE] at hfactor
  rcases hquot with hquot | hquot <;> rw [hquot] at hfactor <;> omega

/-- The automorphism coefficient of the full-translation bottom row fits
the fixed `2^384` allowance of the two-sign source. -/
theorem degreeThreeFourBlock_twoSign_fullTranslation_aut_le
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (hfull : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 4) :
    (Nat.card (preE7NonPairAction w U ≃*
        preE7NonPairAction w U) : ℝ) ≤ (2 : ℝ) ^ (384 : ℝ) := by
  have horder := degreeThreeFourBlock_twoSign_fullTranslation_order_le
    block P hr hs hcomponent hbinary htwo hfull
  have haut := mulEquiv_card_le_two_pow_sq_of_order 12 horder
  have hcast :
      (Nat.card (preE7NonPairAction w U ≃*
          preE7NonPairAction w U) : ℝ) ≤
        (2 : ℝ) ^ (12 * 12 : ℕ) := by
    exact_mod_cast haut
  calc
    (Nat.card (preE7NonPairAction w U ≃*
        preE7NonPairAction w U) : ℝ) ≤
        (2 : ℝ) ^ (12 * 12 : ℕ) := hcast
    _ ≤ (2 : ℝ) ^ (384 : ℕ) := by norm_num
    _ = (2 : ℝ) ^ (384 : ℝ) := (Real.rpow_natCast 2 384).symm

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
