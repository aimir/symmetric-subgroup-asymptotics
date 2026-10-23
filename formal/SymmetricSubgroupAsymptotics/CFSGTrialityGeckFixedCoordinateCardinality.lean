import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedTailCardinality
import SymmetricSubgroupAsymptotics.CFSGTrialityFixedField

/-! The fixed coordinate group of each ACTUAL height layer has one
q-parameter for each long orbit and one q^3-parameter for each short
orbit. The equivalence retains the literal Frobenius triples. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedCoordinateCardinality
open CFSGTrialityGeckFixedTailCardinality CFSGTrialityFixedField
open CFSGTrialityGeckFixedCoordinateDecomposition CFSGTrialityGeckFixedCoordinateParameters
open CFSGTrialityGeckWordCoordinateTwist CFSGTrialityGeckWordRootIndex
open CFSGTrialityD4PositiveRootOrbits CFSGTrialityD4PositiveRootIndex
open CFSGTrialityGeckSectionRootLabels CFSGIntegerHeightSign
open CFSGSerreOrdinaryTwists

abbrev Parameters (q : CFSG.PrimePower) (h : ℤ) :=
  (LongAt h → fixedField q) × (ShortAt h → q.Extension 3)

def coordinates (q : CFSG.PrimePower) (h : ℤ) (p : Parameters q h) :
    WordHeightIndex h → Multiplicative (q.Extension 3)
  | ⟨Sum.inl s,hj⟩ => Multiplicative.ofAdd
      (p.1 ⟨s,(long_height s).symm.trans hj⟩).val
  | ⟨Sum.inr (s,k),hj⟩ => Multiplicative.ofAdd
      (![p.2 ⟨s,(short_label_height s k).symm.trans hj⟩,
        definingFieldAutomorphism q 3 (p.2 ⟨s,(short_label_height s k).symm.trans hj⟩),
        definingFieldAutomorphism q 3 (definingFieldAutomorphism q 3
          (p.2 ⟨s,(short_label_height s k).symm.trans hj⟩))] k)

theorem coordinates_long (q : CFSG.PrimePower) (h : ℤ) (p : Parameters q h)
    (s : Fin 3) (hs : ![(1:ℤ),4,5] s = h) :
    coordinates q h p (longHeightIndex s hs) = Multiplicative.ofAdd (p.1 ⟨s,hs⟩).val := rfl

theorem coordinates_short (q : CFSG.PrimePower) (h : ℤ) (p : Parameters q h)
    (s k : Fin 3) (hs : ![(1:ℤ),2,3] s = h) :
    coordinates q h p (shortHeightIndex s k hs) = Multiplicative.ofAdd
      (![p.2 ⟨s,hs⟩,definingFieldAutomorphism q 3 (p.2 ⟨s,hs⟩),
        definingFieldAutomorphism q 3 (definingFieldAutomorphism q 3 (p.2 ⟨s,hs⟩))] k) := rfl

theorem coordinates_step (q : CFSG.PrimePower) (h : ℤ) (p : Parameters q h)
    (j : WordHeightIndex h) :
    coordinates q h p (heightCycle h j) =
      fieldParameterAut (q.Extension 3) (definingFieldAutomorphism q 3) (coordinates q h p j) := by
  rcases j with ⟨s | ⟨s,k⟩,hj⟩
  · have hs : ![(1:ℤ),4,5] s = h := (long_height s).symm.trans hj
    have he : (⟨Sum.inl s,hj⟩ : WordHeightIndex h) = longHeightIndex s hs := Subtype.ext rfl
    rw [he,heightCycle_long,coordinates_long]
    apply congrArg Multiplicative.ofAdd
    exact (p.1 ⟨s,hs⟩).property.symm
  · have hs : ![(1:ℤ),2,3] s = h := (short_label_height s k).symm.trans hj
    have he : (⟨Sum.inr (s,k),hj⟩ : WordHeightIndex h) = shortHeightIndex s k hs := Subtype.ext rfl
    rw [he,heightCycle_short,coordinates_short,coordinates_short]
    fin_cases k
    · rfl
    · rfl
    · change Multiplicative.ofAdd (p.2 ⟨s,hs⟩) = Multiplicative.ofAdd
        (definingFieldAutomorphism q 3 (definingFieldAutomorphism q 3
          (definingFieldAutomorphism q 3 (p.2 ⟨s,hs⟩))))
      exact congrArg Multiplicative.ofAdd (sigma_thrice q (p.2 ⟨s,hs⟩)).symm

theorem coordinates_fixed (q : CFSG.PrimePower) (h : ℤ) (p : Parameters q h) :
    coordinateTwist (q.Extension 3) (definingFieldAutomorphism q 3) h (coordinates q h p) =
      coordinates q h p := by
  funext j
  have he := coordinates_step q h p ((heightCycle h).symm j)
  rw [Equiv.apply_symm_apply] at he
  exact he.symm

def parameterEquiv (q : CFSG.PrimePower) (h : ℤ) :
    fixedCoordinates (q.Extension 3) (definingFieldAutomorphism q 3) h ≃ Parameters q h where
  toFun c :=
    (fun s => ⟨(c.val (longHeightIndex s.val s.property)).toAdd,
      fixed_long_parameter _ _ h c.val c.property s.val s.property⟩,
    fun s => (c.val (shortHeightIndex s.val 0 s.property)).toAdd)
  invFun p := ⟨coordinates q h p,coordinates_fixed q h p⟩
  left_inv c := by
    apply Subtype.ext
    funext j
    dsimp only
    rcases j with ⟨s | ⟨s,k⟩,hj⟩
    · have hs : ![(1:ℤ),4,5] s = h := (long_height s).symm.trans hj
      have he : (⟨Sum.inl s,hj⟩ : WordHeightIndex h) = longHeightIndex s hs := Subtype.ext rfl
      rw [he,coordinates_long]
      rfl
    · have hs : ![(1:ℤ),2,3] s = h := (short_label_height s k).symm.trans hj
      have he : (⟨Sum.inr (s,k),hj⟩ : WordHeightIndex h) = shortHeightIndex s k hs := Subtype.ext rfl
      rw [he,coordinates_short]
      apply (Multiplicative.toAdd : Multiplicative (q.Extension 3) ≃ q.Extension 3).injective
      exact (fixed_short_parameters _ _ h c.val c.property s hs k).symm
  right_inv p := by
    apply Prod.ext
    · funext s
      apply Subtype.ext
      rfl
    · funext s
      rfl

theorem fixedCoordinates_card (q : CFSG.PrimePower) (h : ℤ) :
    Nat.card (fixedCoordinates (q.Extension 3) (definingFieldAutomorphism q 3) h) =
      q.order ^ (Nat.card (LongAt h) + 3 * Nat.card (ShortAt h)) := by
  rw [Nat.card_congr (parameterEquiv q h)]
  simp only [Parameters,Nat.card_prod,Nat.card_fun,fixedField_card,
    CFSGTrialityTripleFixedRoots.extension_three_card,←pow_mul,←pow_add]

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedCoordinateCardinality
