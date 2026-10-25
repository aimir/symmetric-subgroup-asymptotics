import SymmetricSubgroupAsymptotics.WreathCycleClassCode

/-! Uniform full-wreath bounds for actual two- and three-cycle actions.
The same arbitrary coefficient group is retained throughout. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.WreathShortCycleClassBound
open WreathCycleGaugeConjugacy WreathCycleClassCode
variable {C Q I : Type*} [Group C] [Group Q] [MulAction Q I]
  [Finite C] [Finite Q] [Finite I]

theorem pair_class_card_le (e : Q → (Fin 2 ≃ I))
    (h : ∀ q, q ≠ 1 → q⁻¹ • e q 0=e q 1 ∧ q⁻¹ • e q 1=e q 0) :
    Nat.card (ConjClasses (PermutationalWreathProduct C Q I)) ≤
      Nat.card (ConjClasses C)^2+(Nat.card Q-1)*Nat.card (ConjClasses C) := by
  have hcard : Nat.card I=2 := by simpa using (Nat.card_congr (e 1)).symm
  rw [← hcard]
  apply class_card_le (fun q f => f (e q 0)*f (e q 1))
  intro q hq f g hg
  exact isConj_of_pair_cycle ⟨f,q⟩ ⟨g,q⟩ rfl (e q) (h q hq).1 (h q hq).2 hg

theorem triple_class_card_le (e : Q → (Fin 3 ≃ I))
    (h : ∀ q, q ≠ 1 → q⁻¹ • e q 0=e q 1 ∧
      q⁻¹ • e q 1=e q 2 ∧ q⁻¹ • e q 2=e q 0) :
    Nat.card (ConjClasses (PermutationalWreathProduct C Q I)) ≤
      Nat.card (ConjClasses C)^3+(Nat.card Q-1)*Nat.card (ConjClasses C) := by
  have hcard : Nat.card I=3 := by simpa using (Nat.card_congr (e 1)).symm
  rw [← hcard]
  apply class_card_le (fun q f => f (e q 0)*f (e q 1)*f (e q 2))
  intro q hq f g hg
  exact isConj_of_triple_cycle ⟨f,q⟩ ⟨g,q⟩ rfl (e q)
    (h q hq).1 (h q hq).2.1 (h q hq).2.2 hg

end SymmetricSubgroupAsymptotics.WreathShortCycleClassBound
