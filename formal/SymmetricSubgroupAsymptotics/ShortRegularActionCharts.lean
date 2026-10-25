import SymmetricSubgroupAsymptotics.PrimitiveFourPointComponentClassData
import Mathlib.GroupTheory.OrderOfElement

/-! Actual regular actions of order two or three admit short cycle
charts for each nonidentity element. The charts use the original
action and orbit map; no permutation-action catalogue is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.ShortRegularActionCharts

variable {Q I : Type} [Group Q] [MulAction Q I]
    [Finite Q] [Finite I] [MulAction.IsPretransitive Q I]

theorem orbitMap_bijective (i : I) (hc : Nat.card Q = Nat.card I) :
    Function.Bijective (fun q : Q => q • i) := by
  apply (Nat.bijective_iff_surjective_and_card _).mpr
  exact ⟨fun j => MulAction.exists_smul_eq Q i j,hc⟩

theorem exists_pair_chart (hQ : Nat.card Q = 2) (hI : Nat.card I = 2)
    (i : I) (q : Q) (hq : q ≠ 1) :
    ∃ e : Fin 2 ≃ I, q⁻¹ • e 0 = e 1 ∧ q⁻¹ • e 1 = e 0 := by
  have hqinv : q⁻¹ ≠ 1 := inv_ne_one.mpr hq
  have hpow : q⁻¹ * q⁻¹ = 1 := by
    have h := pow_card_eq_one' (x := q⁻¹)
    simpa only [hQ,pow_two] using h
  let f : Fin 2 → Q := ![1,q⁻¹]
  have hf : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [f]
  let eQ : Fin 2 ≃ Q := Equiv.ofBijective f
    ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf,by simpa only [Nat.card_fin,hQ]⟩)
  let e := eQ.trans (Equiv.ofBijective (fun g : Q => g • i)
    (orbitMap_bijective i (hQ.trans hI.symm)))
  refine ⟨e,?_,?_⟩
  · change q⁻¹ • ((1 : Q) • i) = q⁻¹ • i
    rw [one_smul]
  · change q⁻¹ • (q⁻¹ • i) = (1 : Q) • i
    rw [← mul_smul,hpow]

theorem exists_triple_chart (hQ : Nat.card Q = 3) (hI : Nat.card I = 3)
    (i : I) (q : Q) (hq : q ≠ 1) :
    ∃ e : Fin 3 ≃ I, q⁻¹ • e 0 = e 1 ∧
      q⁻¹ • e 1 = e 2 ∧ q⁻¹ • e 2 = e 0 := by
  have hqinv : q⁻¹ ≠ 1 := inv_ne_one.mpr hq
  have hpow : (q⁻¹ * q⁻¹) * q⁻¹ = 1 := by
    have h := pow_card_eq_one' (x := q⁻¹)
    simpa only [hQ,pow_succ,pow_zero,one_mul] using h
  have hsquare : q⁻¹ * q⁻¹ ≠ 1 := by
    intro hs
    rw [hs,one_mul] at hpow
    exact hqinv hpow
  have hdistinct : q⁻¹ * q⁻¹ ≠ q⁻¹ := by
    intro hs
    have h : q⁻¹ = 1 := by
      apply mul_right_cancel (b := q⁻¹)
      simpa only [one_mul] using hs
    exact hqinv h
  let f : Fin 3 → Q := ![1,q⁻¹,q⁻¹ * q⁻¹]
  have hf : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> dsimp only [f] at hab
    all_goals first
      | rfl
      | exact (hqinv hab).elim
      | exact (hqinv hab.symm).elim
      | exact (hsquare hab).elim
      | exact (hsquare hab.symm).elim
      | exact (hdistinct hab).elim
      | exact (hdistinct hab.symm).elim
  let eQ : Fin 3 ≃ Q := Equiv.ofBijective f
    ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf,by simpa only [Nat.card_fin,hQ]⟩)
  let e := eQ.trans (Equiv.ofBijective (fun g : Q => g • i)
    (orbitMap_bijective i (hQ.trans hI.symm)))
  refine ⟨e,?_,?_,?_⟩
  · change q⁻¹ • ((1 : Q) • i) = q⁻¹ • i
    rw [one_smul]
  · change q⁻¹ • (q⁻¹ • i) = (q⁻¹ * q⁻¹) • i
    rw [mul_smul]
  · change q⁻¹ • ((q⁻¹ * q⁻¹) • i) = (1 : Q) • i
    rw [← mul_smul,← mul_assoc,hpow]

end SymmetricSubgroupAsymptotics.ShortRegularActionCharts
