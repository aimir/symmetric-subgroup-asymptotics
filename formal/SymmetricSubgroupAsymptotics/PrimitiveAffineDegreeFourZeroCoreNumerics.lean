import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourZeroCoreSource

/-!
# Numerical capacity for the degree-four zero-core branch

The zero-core structural theorem changes only the terminal comparator: it
has degree equal to the number of actual blocks.  The elementary binary
translation layer and its coefficient are the same as in the regular
degree-four calculation.  Thus the standard bound `H <= 2s/3` supplies the
full pre-E7 margin without any assumption on the local complement order.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
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

/-- The common zero-core numerical construction from a `2s/3` capacity
bound. -/
noncomputable def degreeFourZeroCoreSource_of_capacity
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (hcapacity : ∀ H : ℝ,
      TraceyRefinedInducedCapacityBounds 2 2 (Nat.card block.Points) H →
        H ≤ (2 : ℝ) * Nat.card block.Points / 3) :
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
  have hw : w = 4 * Nat.card block.Points := by
    simpa only [hr] using width_eq block
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
  have hcap : H.capacity ≤ (2 : ℝ) * Nat.card block.Points / 3 :=
    hcapacity H.capacity href
  have hchartp : (elementaryChart block P).p = 2 := by
    simpa only [elementaryChart] using hp
  have heta : Real.logb 2 (elementaryChart block P).p /
      (elementaryChart block P).p * H.capacity ≤
        (Nat.card block.Points : ℝ) / 3 := by
    have hlog : Real.logb 2 ((2 : ℕ) : ℝ) = 1 :=
      Real.logb_self_eq_one (by norm_num)
    calc
      Real.logb 2 (elementaryChart block P).p /
          (elementaryChart block P).p * H.capacity = H.capacity / 2 := by
        rw [hchartp, hlog]
        ring
      _ ≤ ((2 : ℝ) * Nat.card block.Points / 3) / 2 :=
        div_le_div_of_nonneg_right hcap (by norm_num)
      _ = (Nat.card block.Points : ℝ) / 3 := by ring
  have hm : preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - Nat.card block.Points) / 8 -
        Real.logb 2 (elementaryChart block P).p /
          (elementaryChart block P).p * H.capacity := by
    have heven : evenWidth w = w := by
      rw [hw]
      simp only [evenWidth, halfDegree]
      omega
    have hwR : (w : ℝ) = 4 * Nat.card block.Points := by exact_mod_cast hw
    have hsR : (2 : ℝ) ≤ Nat.card block.Points := by
      exact_mod_cast block.degrees_ge_two.2
    calc
      preE7CharacterRho * w =
          preE7CharacterRho * (4 * Nat.card block.Points) := by rw [hwR]
      _ ≤ ((4 * Nat.card block.Points : ℕ) : ℝ) / 8 -
          (Nat.card block.Points : ℝ) / 8 -
          (Nat.card block.Points : ℝ) / 3 := by
        unfold preE7CharacterRho
        push_cast
        nlinarith
      _ ≤ ((evenWidth w : ℝ) - Nat.card block.Points) / 8 -
          Real.logb 2 (elementaryChart block P).p /
            (elementaryChart block P).p * H.capacity := by
        have hevenR : (evenWidth w : ℝ) = (w : ℝ) := by
          exact_mod_cast heven
        rw [hevenR, hwR]
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
  have hcoeff : ∀ b : ℕ, H.coefficient ≤
      (2 : ℝ) ^ (affineComponentWidthCost w +
        8 * (w : ℝ) * Real.logb 2 (b + 1)) :=
    degreeFourTranslationCoefficient_bound
      (Nat.card block.Points) w block.degrees_ge_two.2 hw
      H.coefficient hcoeff₀
  exact degreeFourZeroCoreSource_of_jointCapacity block P hr hD H hm hcoeff

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
