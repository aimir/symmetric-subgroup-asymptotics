import SymmetricSubgroupAsymptotics.ShortRegularActionCharts
import SymmetricSubgroupAsymptotics.WreathShortCycleClassBound

/-! Loose full-wreath class bounds for the actual regular two- and
three-point top actions, with an arbitrary coefficient group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.WreathRegularSmallTopClassBound

variable {C Q I : Type} [Group C] [Group Q] [MulAction Q I]
    [Finite C] [Finite Q] [Finite I] [MulAction.IsPretransitive Q I]

theorem pair_class_card_le (hQ : Nat.card Q = 2) (hI : Nat.card I = 2) :
    Nat.card (ConjClasses (PermutationalWreathProduct C Q I)) ≤
      Nat.card (ConjClasses C) ^ 2 + Nat.card (ConjClasses C) := by
  let points : Fin 2 ≃ I := (Finite.equivFinOfCardEq hI).symm
  let e : Q → (Fin 2 ≃ I) := fun q => if hq : q = 1 then points else
    Classical.choose (ShortRegularActionCharts.exists_pair_chart hQ hI (points 0) q hq)
  have h : ∀ q, q ≠ 1 → q⁻¹ • e q 0 = e q 1 ∧ q⁻¹ • e q 1 = e q 0 := by
    intro q hq
    dsimp only [e]
    rw [dif_neg hq]
    exact Classical.choose_spec
      (ShortRegularActionCharts.exists_pair_chart hQ hI (points 0) q hq)
  have hc := WreathShortCycleClassBound.pair_class_card_le (C := C) e h
  simpa only [hQ,Nat.reduceSub,one_mul] using hc

theorem triple_class_card_le (hQ : Nat.card Q = 3) (hI : Nat.card I = 3) :
    Nat.card (ConjClasses (PermutationalWreathProduct C Q I)) ≤
      Nat.card (ConjClasses C) ^ 3 + 2 * Nat.card (ConjClasses C) := by
  let points : Fin 3 ≃ I := (Finite.equivFinOfCardEq hI).symm
  let e : Q → (Fin 3 ≃ I) := fun q => if hq : q = 1 then points else
    Classical.choose (ShortRegularActionCharts.exists_triple_chart hQ hI (points 0) q hq)
  have h : ∀ q, q ≠ 1 → q⁻¹ • e q 0 = e q 1 ∧
      q⁻¹ • e q 1 = e q 2 ∧ q⁻¹ • e q 2 = e q 0 := by
    intro q hq
    dsimp only [e]
    rw [dif_neg hq]
    exact Classical.choose_spec
      (ShortRegularActionCharts.exists_triple_chart hQ hI (points 0) q hq)
  have hc := WreathShortCycleClassBound.triple_class_card_le (C := C) e h
  simpa only [hQ,Nat.reduceSub] using hc

end SymmetricSubgroupAsymptotics.WreathRegularSmallTopClassBound
