import SymmetricSubgroupAsymptotics.BinaryCarrierRadicalStructure16T1547
import SymmetricSubgroupAsymptotics.NormalSubgroupSaturationCenter
import SymmetricSubgroupAsymptotics.BinaryCarrierRadicalSaturation16T1547
import SymmetricSubgroupAsymptotics.BinaryCarrierFormTransport16T1547
import SymmetricSubgroupAsymptotics.PrimeDerivedIntersectionForms

/-! Exact original quotient-center preimages throughout the small
relative radical of 16T1547. The original form family excludes directions
outside D; the original commutator saturation excludes D\R when M<R.
No enumeration of original normal subgroups or normal planes is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics.BinaryCarrierRadicalCenter16T1547

abbrev Original := BinaryCarrierRadicalStructure16T1547.Original
abbrev D := commutator Original
abbrev R := primeRelativeRadical 2 D
abbrev Z := BinaryCarrierRadicalStructure16T1547.Z
private abbrev hker := BinaryCarrierDerived16T1547.evaluationKernel_eq_commutator
private abbrev g := BinaryActionData16.node1547Generators
private abbrev ambient := closureGenerators g
private abbrev rows := BinaryCarrierDerivedRadical16T1547.elements
private abbrev ambientRows := BinaryCarrierDerivedRadical16T1547.ambientRows

/-- Every original derived character vanishes on M≤R. The actual
independent-pair radical bound therefore forces its entire quotient-center
image to be zero in the original evaluation quotient. -/
theorem centerPreimage_le_derived (M : Subgroup Original) [M.Normal] (hM : M ≤ R) :
    quotientCenterPreimage M ≤ D := by
  apply (primeDerivedImage_eq_bot_iff_le_commutator 2 hker _).mp
  by_contra hW
  have hle := Submodule.finrank_mono
    (derivedCharactersVanishingOn_le_center_joint 2 hker M)
  rw [derivedCharactersVanishingOn_eq_top_of_le_radical 2 M hM,
    finrank_top, BinaryCarrierDerivedRadical16T1547.relative_character_rank] at hle
  have hone := linearJointAnnihilator_finrank_le_one
    (derivedEvaluationBilinearMap 2 hker) (primeDerivedImage 2 (quotientCenterPreimage M))
    BinaryCarrierFormTransport16T1547.actual_form_ker_inf_eq_bot_of_independent hW
  omega

theorem centerPreimage_le_radical (M : Subgroup Original) [M.Normal]
    (hM : M ≤ R) (hnot : ¬ R ≤ M) : quotientCenterPreimage M ≤ R :=
  BinaryCarrierRadicalSaturation16T1547.certificate.quotientCenterPreimage_le
    BinaryCarrierRadicalSaturation16T1547.nonempty_words M hnot
    (centerPreimage_le_derived M hM)

theorem radical_le_centerPreimage (M : Subgroup Original) [M.Normal] (hZM : Z ≤ M) :
    R ≤ quotientCenterPreimage M := by
  intro x hx
  apply (mem_quotientCenterPreimage_iff_all_commutators M x).mpr
  intro y
  apply hZM
  exact BinaryCarrierRadicalStructure16T1547.mixed_eq_Z.le
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
    (∀ (j : Fin 6) (x : Fin 16), ⁅ambientRows 0, g j⁆ x = x) →
      (0 : Fin 8) = 0 ∨ (0 : Fin 8) = 1 := fun _ => Or.inl rfl
private theorem fixed_row_cases1 :
    (∀ (j : Fin 6) (x : Fin 16), ⁅ambientRows 1, g j⁆ x = x) →
      (1 : Fin 8) = 0 ∨ (1 : Fin 8) = 1 := fun _ => Or.inr rfl
private theorem fixed_row_cases2 :
    (∀ (j : Fin 6) (x : Fin 16), ⁅ambientRows 2, g j⁆ x = x) →
      (2 : Fin 8) = 0 ∨ (2 : Fin 8) = 1 := by decide +kernel
private theorem fixed_row_cases3 :
    (∀ (j : Fin 6) (x : Fin 16), ⁅ambientRows 3, g j⁆ x = x) →
      (3 : Fin 8) = 0 ∨ (3 : Fin 8) = 1 := by decide +kernel
private theorem fixed_row_cases4 :
    (∀ (j : Fin 6) (x : Fin 16), ⁅ambientRows 4, g j⁆ x = x) →
      (4 : Fin 8) = 0 ∨ (4 : Fin 8) = 1 := by decide +kernel
private theorem fixed_row_cases5 :
    (∀ (j : Fin 6) (x : Fin 16), ⁅ambientRows 5, g j⁆ x = x) →
      (5 : Fin 8) = 0 ∨ (5 : Fin 8) = 1 := by decide +kernel
private theorem fixed_row_cases6 :
    (∀ (j : Fin 6) (x : Fin 16), ⁅ambientRows 6, g j⁆ x = x) →
      (6 : Fin 8) = 0 ∨ (6 : Fin 8) = 1 := by decide +kernel
private theorem fixed_row_cases7 :
    (∀ (j : Fin 6) (x : Fin 16), ⁅ambientRows 7, g j⁆ x = x) →
      (7 : Fin 8) = 0 ∨ (7 : Fin 8) = 1 := by decide +kernel

private theorem fixed_row_cases (i : Fin 8) :
    (∀ (j : Fin 6) (x : Fin 16), ⁅ambientRows i, g j⁆ x = x) → i = 0 ∨ i = 1 := by
  fin_cases i
  · exact fixed_row_cases0
  · exact fixed_row_cases1
  · exact fixed_row_cases2
  · exact fixed_row_cases3
  · exact fixed_row_cases4
  · exact fixed_row_cases5
  · exact fixed_row_cases6
  · exact fixed_row_cases7

theorem centerPreimage_bot_eq_Z : quotientCenterPreimage (⊥ : Subgroup Original) = Z := by
  have hnot : ¬ R ≤ (⊥ : Subgroup Original) := by
    intro h
    have hc := Subgroup.card_le_of_le h
    rw [BinaryCarrierDerivedRadical16T1547.card_relative_radical, Subgroup.card_bot] at hc
    omega
  apply le_antisymm
  · intro x hx
    have hxR := centerPreimage_le_radical (⊥ : Subgroup Original) bot_le hnot hx
    obtain ⟨i, hi⟩ := BinaryCarrierRadicalHead16T1547.certificate.rows_cover x hxR
    change rows i = x at hi
    have hfix : ∀ (j : Fin 6) (y : Fin 16), ⁅ambientRows i, g j⁆ y = y := by
      intro j y
      have hm := (mem_quotientCenterPreimage_iff_all_commutators
        (⊥ : Subgroup Original) x).mp hx (ambient j)
      have he : ⁅x, ambient j⁆ = 1 := hm
      rw [← hi] at he
      have hp := congrArg (fun u : Original => (u : Equiv.Perm (Fin 16)) y) he
      change ⁅(rows i : Equiv.Perm (Fin 16)), g j⁆ y = y at hp
      rwa [BinaryCarrierDerivedRadical16T1547.elements_coe] at hp
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
      (BinaryCarrierRadicalStructure16T1547.Z_le_center hx) y).symm

theorem center_card_mul_of_between (M : Subgroup Original) [M.Normal]
    (hM : M ≤ R) (hZM : Z ≤ M) (hnot : ¬ R ≤ M) :
    Nat.card (Subgroup.center (Original ⧸ M)) * Nat.card M = 8 := by
  have h := quotientCenter_card_mul M
  rw [centerPreimage_eq_radical M hM hZM hnot,
    BinaryCarrierDerivedRadical16T1547.card_relative_radical] at h
  exact h

end SymmetricSubgroupAsymptotics.BinaryCarrierRadicalCenter16T1547
