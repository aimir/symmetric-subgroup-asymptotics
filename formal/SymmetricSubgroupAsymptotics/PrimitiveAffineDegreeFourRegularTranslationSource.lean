import SymmetricSubgroupAsymptotics.PrimitiveAffineTopTranslationSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveDegreeFourS4Exhaustion

/-!
# Regular degree-four affine components at the literal block top

When a primitive affine component of degree four has order four, it is its
regular translation subgroup.  The local complement quotient is therefore
trivial, and the one elementary layer can stop at the faithful action on the
literal set of blocks.

Tracey's prime-to-characteristic estimate closes every exceptional block
count with an odd prime divisor.  For a pure binary count `2^e`, the
prime-power estimate and the published central-binomial inequality close
every `e >= 5`.  Inside the existing degree-four exception menu, the exact
residual is consequently `2, 4, 8, 16`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- The one-layer Tracey coefficient for a two-dimensional binary
translation module is bounded by the standard affine width cost. -/
theorem degreeFourTranslationCoefficient_bound
    (s w : ℕ) (hs : 2 ≤ s) (hw : w = 4 * s) (C : ℝ)
    (hC : C ≤ (2 : ℝ) ^
      traceyAffineCoefficientExponent 2 s
        (traceyInducedGeneratorCeiling 2 s)
        (traceyPermutationGeneratorCeiling w) w 2) :
    ∀ b : ℕ, C ≤
      (2 : ℝ) ^ (affineComponentWidthCost w +
        8 * (w : ℝ) * Real.logb 2 (b + 1)) := by
  intro b
  let A : ℕ := traceyAffineCoefficientExponent 2 s
    (traceyInducedGeneratorCeiling 2 s)
    (traceyPermutationGeneratorCeiling w) w 2
  let q : ℝ := Real.sqrt (Real.logb 2 (s : ℝ))
  let B : ℝ := 4 * s * w / q +
    s * (traceyPermutationGeneratorCeiling w + 2) + w
  have hqpos : 0 < q := by
    dsimp [q]
    exact Real.sqrt_pos.2
      (Real.logb_pos (by norm_num) (by exact_mod_cast hs))
  have hA0 : 0 ≤ 4 * (s : ℝ) ^ 2 / q := by positivity
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  have hraw := traceyAffineCoefficientExponent_log_le
    2 s (traceyPermutationGeneratorCeiling w) w 2
    Nat.prime_two hs
  have hcore : (A : ℝ) ≤
      4 * (s : ℝ) ^ 2 / q * (2 : ℝ) ^ 2 + B * 2 := by
    simpa only [A, q, B,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
      one_mul, mul_one, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] using hraw
  have hlogb : 0 ≤ Real.logb 2 (b + 1) :=
    Real.logb_nonneg (by norm_num)
      (by exact_mod_cast (show 1 ≤ b + 1 by omega))
  have hexp : (A : ℝ) ≤ affineComponentCoefficientExponent 4 s w b := by
    calc
      (A : ℝ) ≤ 4 * (s : ℝ) ^ 2 / q * (2 : ℝ) ^ 2 + B * 2 := hcore
      _ ≤ 4 * (s : ℝ) ^ 2 / q * (9 : ℝ) ^ 2 + B * 9 := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left (by norm_num) hA0
        · apply mul_le_mul_of_nonneg_left (by norm_num) hB0
      _ ≤ 4 * (s : ℝ) ^ 2 / q * (9 : ℝ) ^ 2 + B * 9 +
          3 * s * 9 + 2 * s * 9 * Real.logb 2 (b + 1) := by
        have htail : 0 ≤ 3 * (s : ℝ) * 9 +
            2 * s * 9 * Real.logb 2 (b + 1) := by positivity
        linarith
      _ = affineComponentCoefficientExponent 4 s w b := by
        norm_num [affineComponentCoefficientExponent, q, B, Nat.log]
  calc
    C ≤ (2 : ℝ) ^ A := by simpa only [A] using hC
    _ = (2 : ℝ) ^ (A : ℝ) := by
      rw [Real.rpow_natCast]
    _ ≤ (2 : ℝ) ^ affineComponentCoefficientExponent 4 s w b :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ ≤ (2 : ℝ) ^ (affineComponentWidthCost w +
        8 * (w : ℝ) * Real.logb 2 (b + 1)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (affineComponentCoefficientExponent_le_widthCost
          4 s w b (by norm_num) hs hw)

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)

variable [Nontrivial block.Fibre]

private abbrev blocks := Nat.card block.Points

/-- Common construction: a regular degree-four component gives a trivial
local quotient, and any capacity at most `2s/3` leaves the required strict
pre-E7 margin at the literal block top. -/
noncomputable def degreeFourRegularTranslationSource_of_capacity
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 4)
    (hcomponent : Nat.card block.Component = 4)
    (hcapacity : ∀ H : ℝ,
      TraceyRefinedInducedCapacityBounds 2 2 (blocks block) H →
        H ≤ (2 : ℝ) * blocks block / 3) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  let C₀ := P.elementaryChart block.component_preprimitive
  letI : Fact P.p.Prime := C₀.primeFact
  letI : AddCommGroup C₀.V := C₀.addCommGroup
  letI : Module (ZMod P.p) C₀.V := C₀.module
  letI : FiniteDimensional (ZMod P.p) C₀.V := C₀.finiteDimensional
  letI : Finite C₀.V := Finite.of_injective
    (fun v : C₀.V => C₀.equiv.symm (Multiplicative.ofAdd v))
    C₀.equiv.symm.injective
  have hdegree₀ : Nat.card block.Fibre = P.p ^ C₀.d := by
    simpa [PrimitiveAffineProfile.ElementaryChart.d] using
      P.degree_eq_prime_pow_finrank C₀.equiv (origin block)
  have hdegree : 4 = P.p ^ C₀.d := hr.symm.trans hdegree₀
  have hpd := prime_pow_positive_injective (d := C₀.d) (e := 2)
    P.p_prime Nat.prime_two C₀.d_pos (by norm_num)
    (hdegree.symm.trans (by norm_num))
  have hp : P.p = 2 := hpd.1
  have hd : C₀.d = 2 := hpd.2
  have hdim : Module.finrank (ZMod P.p) (chart block P).V = 2 := by
    simpa only [chart, C₀, PrimitiveAffineProfile.ElementaryChart.d] using hd
  have hw : w = 4 * blocks block := by
    simpa only [blocks, hr] using width_eq block
  let S := initialState hTraceyPerm block
  let C := localTranslationChart block P
  let raw := (affineCapacityInput hTraceyHalf hTraceyLog hTraceyRefined block)
    S (LocalQuotient block P) (localMap block P)
      (localMap_surjective block P) C
  let H := Classical.choose raw
  have hH := Classical.choose_spec raw
  have href := hH.2.2.1
  change TraceyRefinedInducedCapacityBounds P.p
    (Module.finrank (ZMod P.p) (chart block P).V)
    (Fintype.card block.Points) H.capacity at href
  rw [hdim, Fintype.card_eq_nat_card, hp] at href
  have hcap : H.capacity ≤ (2 : ℝ) * blocks block / 3 :=
    hcapacity H.capacity href
  have hchartp : (elementaryChart block P).p = 2 := by
    simpa only [elementaryChart] using hp
  have heta : Real.logb 2 (elementaryChart block P).p /
      (elementaryChart block P).p * H.capacity ≤
        (blocks block : ℝ) / 3 := by
    rw [hchartp, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    norm_num
    linarith
  have hm : preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - Nat.card block.Points) / 8 -
        Real.logb 2 (elementaryChart block P).p /
          (elementaryChart block P).p * H.capacity := by
    have heven : evenWidth w = w := by
      rw [hw]
      simp only [evenWidth, halfDegree]
      omega
    have hwR : (w : ℝ) = 4 * blocks block := by exact_mod_cast hw
    have hsR : (2 : ℝ) ≤ blocks block := by
      exact_mod_cast block.degrees_ge_two.2
    calc
      preE7CharacterRho * w = preE7CharacterRho * (4 * blocks block) := by
        rw [hwR]
      _ ≤ ((4 * blocks block : ℕ) : ℝ) / 8 -
          (blocks block : ℝ) / 8 - (blocks block : ℝ) / 3 := by
        unfold preE7CharacterRho
        push_cast
        nlinarith
      _ ≤ ((evenWidth w : ℝ) - Nat.card block.Points) / 8 -
          Real.logb 2 (elementaryChart block P).p /
            (elementaryChart block P).p * H.capacity := by
        rw [heven, hw]
        simp only [blocks]
        push_cast
        linarith
  have hcoeff₀ := hH.2.2.2.2
  change H.coefficient ≤ (P.p : ℝ) ^
      traceyAffineCoefficientExponent
        (Module.finrank (ZMod P.p) (chart block P).V)
        (Fintype.card block.Points)
        (traceyInducedGeneratorCeiling
          (Module.finrank (ZMod P.p) (chart block P).V)
          (Fintype.card block.Points))
        (traceyPermutationGeneratorCeiling w) w P.p at hcoeff₀
  rw [hdim, Fintype.card_eq_nat_card, hp] at hcoeff₀
  have hD : ∀ b : ℕ, H.coefficient ≤
      (2 : ℝ) ^ (affineComponentWidthCost w +
        8 * (w : ℝ) * Real.logb 2 (b + 1)) :=
    degreeFourTranslationCoefficient_bound
      (blocks block) w block.degrees_ge_two.2 hw H.coefficient hcoeff₀
  have hV : Nat.card P.V = 4 :=
    (P.card_eq (origin block)).trans hr
  have hcomponentV : Nat.card block.Component = Nat.card P.V :=
    hcomponent.trans hV.symm
  have hlocal : ∀ q : LocalQuotient block P, q = 1 :=
    localQuotient_eq_one_of_component_card_eq_translation block P hcomponentV
  exact topTranslationLayerSource block P hlocal H
    block.degrees_ge_two.2 hm hD

/-- An odd prime divisor of the block count gives `H ≤ 2s/q ≤ 2s/3`,
which closes the regular degree-four translation cell. -/
noncomputable def degreeFourRegularTranslationSource_of_oddPrime
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 4)
    (hcomponent : Nat.card block.Component = 4)
    (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (hdiv : q ∣ blocks block) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  apply degreeFourRegularTranslationSource_of_capacity block P
    hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hr hcomponent
  intro H href
  have hq3 : 3 ≤ q := by omega
  have h := href.primeTo q 1 hq hq2 (by norm_num) (by simpa using hdiv)
  calc
    H ≤ (2 : ℝ) * blocks block / q := by simpa using h
    _ ≤ (2 : ℝ) * blocks block / 3 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num)
        (by exact_mod_cast hq3)

/-- A pure binary block count `2^e` closes from exponent five onward. -/
noncomputable def degreeFourRegularTranslationSource_of_binaryPower
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 4)
    (hcomponent : Nat.card block.Component = 4)
    (e : ℕ) (he : 5 ≤ e) (hs : blocks block = 2 ^ e) :
    PreE7RankTailSourceOrYonedaTopData w U := by
  apply degreeFourRegularTranslationSource_of_capacity block P
    hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hr hcomponent
  intro H href
  have he1 : 1 ≤ e := by omega
  have h := href.primePower 2 e Nat.prime_two he1 hs
  have hmiddleNat := binary_middle_le_five_sixteenths e he
  have hmiddle : (e.choose (e / 2) : ℝ) / (2 : ℝ) ^ e ≤ 5 / 16 := by
    have hcast : (16 : ℝ) * e.choose (e / 2) ≤ 5 * (2 : ℝ) ^ e := by
      exact_mod_cast hmiddleNat
    have hpow : (0 : ℝ) < (2 : ℝ) ^ e := by positivity
    apply (div_le_iff₀ hpow).2
    nlinarith
  have hs0 : (0 : ℝ) ≤ blocks block := by positivity
  calc
    H ≤ (2 : ℝ) * blocks block * e.choose (e / 2) / (2 : ℝ) ^ e := by
      simpa only [Nat.reduceSubDiff, Nat.mul_one] using h
    _ = ((2 : ℝ) * blocks block) *
        ((e.choose (e / 2) : ℝ) / (2 : ℝ) ^ e) := by ring
    _ ≤ ((2 : ℝ) * blocks block) * (5 / 16 : ℝ) :=
      mul_le_mul_of_nonneg_left hmiddle (by positivity)
    _ ≤ (2 : ℝ) * blocks block / 3 := by nlinarith

/-- Exact residual among the existing degree-four capacity exceptions for a
regular translation component. -/
def IsDegreeFourRegularTranslationResidualBlockCount (s : ℕ) : Prop :=
  s = 2 ∨ s = 4 ∨ s = 8 ∨ s = 16

/-- Every regular degree-four member of the old degree-four exception menu
is now a direct top-translation source, except for the four tiny pure binary
block counts. -/
noncomputable def degreeFourRegularTranslationExceptionalExhaustion
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 4)
    (hcomponent : Nat.card block.Component = 4)
    (hs : ComponentSource.IsDegreeFourTwentyFourExceptionalBlockCount
      (blocks block)) :
    PreE7RankTailSourceOrYonedaTopData w U ⊕
      PLift (IsDegreeFourRegularTranslationResidualBlockCount (blocks block)) := by
  rcases hs with hpair | h5 | h10 | h15 | h20 | h30 | h60
  · rcases hpair with hbinary | hthree
    · obtain ⟨a, ha1, ha8, ha⟩ := hbinary
      by_cases ha5 : 5 ≤ a
      · exact .inl (degreeFourRegularTranslationSource_of_binaryPower block P
          hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hr hcomponent
          a ha5 ha)
      · have ha4 : a ≤ 4 := by omega
        exact .inr ⟨by
          interval_cases a <;>
            simp_all [IsDegreeFourRegularTranslationResidualBlockCount]⟩
    · obtain ⟨a, ha10, ha⟩ := hthree
      exact .inl (degreeFourRegularTranslationSource_of_oddPrime block P
        hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hr hcomponent
        3 (by norm_num) (by norm_num) (by
          rw [ha]
          exact dvd_mul_right 3 (2 ^ a)))
  · exact .inl (degreeFourRegularTranslationSource_of_oddPrime block P
      hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hr hcomponent
      5 (by norm_num) (by norm_num) (by rw [h5]))
  · exact .inl (degreeFourRegularTranslationSource_of_oddPrime block P
      hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hr hcomponent
      5 (by norm_num) (by norm_num) (by rw [h10]; norm_num))
  · exact .inl (degreeFourRegularTranslationSource_of_oddPrime block P
      hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hr hcomponent
      3 (by norm_num) (by norm_num) (by rw [h15]; norm_num))
  · exact .inl (degreeFourRegularTranslationSource_of_oddPrime block P
      hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hr hcomponent
      5 (by norm_num) (by norm_num) (by rw [h20]; norm_num))
  · exact .inl (degreeFourRegularTranslationSource_of_oddPrime block P
      hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hr hcomponent
      3 (by norm_num) (by norm_num) (by rw [h30]; norm_num))
  · exact .inl (degreeFourRegularTranslationSource_of_oddPrime block P
      hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm hr hcomponent
      3 (by norm_num) (by norm_num) (by rw [h60]; norm_num))

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
