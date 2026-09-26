import SymmetricSubgroupAsymptotics.BinaryCarrierRadicalStructure16T1332
import SymmetricSubgroupAsymptotics.NormalSubgroupSaturationCenter
import SymmetricSubgroupAsymptotics.BinaryCarrierRadicalSaturation16T1332
import SymmetricSubgroupAsymptotics.BinaryCarrierStarTransport16T1332
import SymmetricSubgroupAsymptotics.PrimeDerivedFullSeparationCenter

/-! Exact original quotient-center preimages throughout the small
relative radical of 16T1332. The original form family excludes directions
outside D; the original commutator saturation excludes D\R when M<R.
No enumeration of original normal subgroups or normal planes is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics.BinaryCarrierRadicalCenter16T1332

abbrev Original := BinaryCarrierRadicalStructure16T1332.Original
abbrev D := commutator Original
abbrev R := primeRelativeRadical 2 D
abbrev Z := BinaryCarrierRadicalStructure16T1332.Z
private abbrev hker := BinaryCarrierDerived16T1332.evaluationKernel_eq_commutator
private abbrev g := BinaryActionData16.node1332Generators
private abbrev ambient := closureGenerators g
private abbrev rows := BinaryCarrierDerivedRadical16T1332.elements
private abbrev ambientRows := BinaryCarrierDerivedRadical16T1332.ambientRows

/-- The complete original star family separates the evaluation space. -/
theorem actual_forms_separate (v : PrimeAbelianization 2 Original)
    (hv : ∀ χ : primeRelativeCharacters 2 D,
      derivedEvaluationBilinearMap 2 hker χ v = 0) : v = 0 := by
  apply BinaryCarrierStarTransport16T1332.evaluationEquiv.injective
  rw [map_zero]
  apply starAlternatingFamily_separates
  intro l y
  obtain ⟨χ, rfl⟩ := BinaryCarrierStarTransport16T1332.characterEquiv.surjective l
  obtain ⟨w, rfl⟩ := BinaryCarrierStarTransport16T1332.evaluationEquiv.surjective y
  rw [← BinaryCarrierStarTransport16T1332.actual_form_eq_star]
  change (derivedEvaluationBilinearMap 2 hker χ v) w = 0
  rw [hv χ]
  rfl

theorem centerPreimage_le_derived (M : Subgroup Original) [M.Normal] (hM : M ≤ R) :
    quotientCenterPreimage M ≤ D :=
  quotientCenterPreimage_le_commutator_of_full_separation 2 hker actual_forms_separate M hM

theorem centerPreimage_le_radical (M : Subgroup Original) [M.Normal]
    (hM : M ≤ R) (hnot : ¬ R ≤ M) : quotientCenterPreimage M ≤ R :=
  BinaryCarrierRadicalSaturation16T1332.certificate.quotientCenterPreimage_le
    BinaryCarrierRadicalSaturation16T1332.nonempty_words M hnot
    (centerPreimage_le_derived M hM)

theorem radical_le_centerPreimage (M : Subgroup Original) [M.Normal] (hZM : Z ≤ M) :
    R ≤ quotientCenterPreimage M := by
  intro x hx
  apply (mem_quotientCenterPreimage_iff_all_commutators M x).mpr
  intro y
  apply hZM
  exact BinaryCarrierRadicalStructure16T1332.mixed_eq_Z.le
    (Subgroup.commutator_mem_commutator hx (Subgroup.mem_top y))

/-- All original normals between Z and R, except R itself, have the SAME
literal center preimage R. Their quotient-center sizes retain |M|. -/
theorem centerPreimage_eq_radical (M : Subgroup Original) [M.Normal]
    (hM : M ≤ R) (hZM : Z ≤ M) (hnot : ¬ R ≤ M) :
    quotientCenterPreimage M = R :=
  le_antisymm (centerPreimage_le_radical M hM hnot) (radical_le_centerPreimage M hZM)

theorem centerPreimage_radical_eq_derived : quotientCenterPreimage R = D := by
  apply le_antisymm (centerPreimage_le_derived R le_rfl)
  intro x hx
  apply (mem_quotientCenterPreimage_iff_all_commutators R x).mpr
  intro y
  exact commutator_mem_primeRelativeRadical 2 D ⟨x, hx⟩ y

private theorem fixed_row_cases0 :
    (∀ (j : Fin 5) (x : Fin 16), ⁅ambientRows 0, g j⁆ x = x) →
      (0 : Fin 4) = 0 ∨ (0 : Fin 4) = 1 := fun _ => Or.inl rfl
private theorem fixed_row_cases1 :
    (∀ (j : Fin 5) (x : Fin 16), ⁅ambientRows 1, g j⁆ x = x) →
      (1 : Fin 4) = 0 ∨ (1 : Fin 4) = 1 := fun _ => Or.inr rfl
private theorem fixed_row_cases2 :
    (∀ (j : Fin 5) (x : Fin 16), ⁅ambientRows 2, g j⁆ x = x) →
      (2 : Fin 4) = 0 ∨ (2 : Fin 4) = 1 := by decide +kernel
private theorem fixed_row_cases3 :
    (∀ (j : Fin 5) (x : Fin 16), ⁅ambientRows 3, g j⁆ x = x) →
      (3 : Fin 4) = 0 ∨ (3 : Fin 4) = 1 := by decide +kernel
private theorem fixed_row_cases (i : Fin 4) :
    (∀ (j : Fin 5) (x : Fin 16), ⁅ambientRows i, g j⁆ x = x) → i = 0 ∨ i = 1 := by
  fin_cases i
  · exact fixed_row_cases0
  · exact fixed_row_cases1
  · exact fixed_row_cases2
  · exact fixed_row_cases3

theorem centerPreimage_bot_eq_Z : quotientCenterPreimage (⊥ : Subgroup Original) = Z := by
  have hnot : ¬ R ≤ (⊥ : Subgroup Original) := by
    intro h
    have hc := Subgroup.card_le_of_le h
    rw [BinaryCarrierDerivedRadical16T1332.card_relative_radical, Subgroup.card_bot] at hc
    omega
  apply le_antisymm
  · intro x hx
    have hxR := centerPreimage_le_radical (⊥ : Subgroup Original) bot_le hnot hx
    obtain ⟨i, hi⟩ := BinaryCarrierRadicalHead16T1332.certificate.rows_cover x hxR
    change rows i = x at hi
    have hfix : ∀ (j : Fin 5) (y : Fin 16), ⁅ambientRows i, g j⁆ y = y := by
      intro j y
      have hm := (mem_quotientCenterPreimage_iff_all_commutators
        (⊥ : Subgroup Original) x).mp hx (ambient j)
      have he : ⁅x, ambient j⁆ = 1 := hm
      rw [← hi] at he
      have hp := congrArg (fun u : Original => (u : Equiv.Perm (Fin 16)) y) he
      change ⁅(rows i : Equiv.Perm (Fin 16)), g j⁆ y = y at hp
      rwa [BinaryCarrierDerivedRadical16T1332.elements_coe] at hp
    rcases fixed_row_cases i hfix with rfl | rfl
    · rw [← hi]
      exact Z.one_mem
    · rw [← hi]
      exact Subgroup.subset_closure (Set.mem_range_self (0 : Fin 1))
  · intro x hx
    apply (mem_quotientCenterPreimage_iff_all_commutators
      (⊥ : Subgroup Original) x).mpr
    intro y
    change ⁅x, y⁆ = 1
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact (Subgroup.mem_center_iff.mp
      (BinaryCarrierRadicalStructure16T1332.Z_le_center hx) y).symm

theorem center_card_mul_of_between (M : Subgroup Original) [M.Normal]
    (hM : M ≤ R) (hZM : Z ≤ M) (hnot : ¬ R ≤ M) :
    Nat.card (Subgroup.center (Original ⧸ M)) * Nat.card M = 4 := by
  have h := quotientCenter_card_mul M
  rw [centerPreimage_eq_radical M hM hZM hnot,
    BinaryCarrierDerivedRadical16T1332.card_relative_radical] at h
  exact h

end SymmetricSubgroupAsymptotics.BinaryCarrierRadicalCenter16T1332
