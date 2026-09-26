import SymmetricSubgroupAsymptotics.BinaryCarrierRadicalHead16T1547

/-! The second relative radical of the actual 16T1547 derived radical
is its original central subgroup of order two. All square and mixed
tests use the eight existing rows and the six original ambient
generators. Consequences apply to every whole-original-group normal
subgroup inside R, without a list of normal planes. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics.BinaryCarrierRadicalStructure16T1547

abbrev Original := BinaryCarrierRadicalHead16T1547.Original
abbrev D := commutator Original
abbrev R := primeRelativeRadical 2 D
abbrev Z := BinaryCarrierRadicalHead16T1547.Z
private abbrev g := BinaryActionData16.node1547Generators
private abbrev ambient := closureGenerators g
private abbrev rows := BinaryCarrierDerivedRadical16T1547.elements
private abbrev ambientRows := BinaryCarrierDerivedRadical16T1547.ambientRows
private abbrev saturation := BinaryCarrierRadicalHead16T1547.certificate

private def mixedHit : Fin 8 → Fin 6 → Bool :=
  ![![false,false,false,false,false,false],
    ![false,false,false,false,false,false],
    ![false,false,false,false,true,false],
    ![false,false,false,true,false,false],
    ![false,false,false,false,true,false],
    ![false,false,false,true,false,false],
    ![false,false,false,true,true,false],
    ![false,false,false,true,true,false]]

private theorem square_pointwise : ∀ (i : Fin 8) (x : Fin 16),
    (ambientRows i ^ 2) x = x := by decide +kernel

private theorem mixed_pointwise0 : ∀ (j : Fin 6) (x : Fin 16),
    ⁅ambientRows 0, g j⁆ x = if mixedHit 0 j then ambientRows 1 x else x := by decide +kernel
private theorem mixed_pointwise1 : ∀ (j : Fin 6) (x : Fin 16),
    ⁅ambientRows 1, g j⁆ x = if mixedHit 1 j then ambientRows 1 x else x := by decide +kernel
private theorem mixed_pointwise2 : ∀ (j : Fin 6) (x : Fin 16),
    ⁅ambientRows 2, g j⁆ x = if mixedHit 2 j then ambientRows 1 x else x := by decide +kernel
private theorem mixed_pointwise3 : ∀ (j : Fin 6) (x : Fin 16),
    ⁅ambientRows 3, g j⁆ x = if mixedHit 3 j then ambientRows 1 x else x := by decide +kernel
private theorem mixed_pointwise4 : ∀ (j : Fin 6) (x : Fin 16),
    ⁅ambientRows 4, g j⁆ x = if mixedHit 4 j then ambientRows 1 x else x := by decide +kernel
private theorem mixed_pointwise5 : ∀ (j : Fin 6) (x : Fin 16),
    ⁅ambientRows 5, g j⁆ x = if mixedHit 5 j then ambientRows 1 x else x := by decide +kernel
private theorem mixed_pointwise6 : ∀ (j : Fin 6) (x : Fin 16),
    ⁅ambientRows 6, g j⁆ x = if mixedHit 6 j then ambientRows 1 x else x := by decide +kernel
private theorem mixed_pointwise7 : ∀ (j : Fin 6) (x : Fin 16),
    ⁅ambientRows 7, g j⁆ x = if mixedHit 7 j then ambientRows 1 x else x := by decide +kernel

private theorem mixed_pointwise (i : Fin 8) : ∀ (j : Fin 6) (x : Fin 16),
    ⁅ambientRows i, g j⁆ x = if mixedHit i j then ambientRows 1 x else x := by
  fin_cases i
  · exact mixed_pointwise0
  · exact mixed_pointwise1
  · exact mixed_pointwise2
  · exact mixed_pointwise3
  · exact mixed_pointwise4
  · exact mixed_pointwise5
  · exact mixed_pointwise6
  · exact mixed_pointwise7

theorem rows_square (i : Fin 8) : rows i ^ 2 = 1 := by
  apply Subtype.ext
  change (rows i : Equiv.Perm (Fin 16)) ^ 2 = 1
  rw [BinaryCarrierDerivedRadical16T1547.elements_coe]
  exact Equiv.ext (square_pointwise i)

theorem rows_mixed (i : Fin 8) (j : Fin 6) :
    ⁅rows i, ambient j⁆ = if mixedHit i j then rows 1 else 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  by_cases h : mixedHit i j = true
  · simp only [h, ↓reduceIte]
    change ⁅(rows i : Equiv.Perm (Fin 16)), g j⁆ x =
      (rows 1 : Equiv.Perm (Fin 16)) x
    rw [BinaryCarrierDerivedRadical16T1547.elements_coe,
      BinaryCarrierDerivedRadical16T1547.elements_coe]
    simpa only [h, ↓reduceIte] using mixed_pointwise i j x
  · simp only [h, ↓reduceIte]
    change ⁅(rows i : Equiv.Perm (Fin 16)), g j⁆ x = x
    rw [BinaryCarrierDerivedRadical16T1547.elements_coe]
    simpa only [h, ↓reduceIte] using mixed_pointwise i j x

private theorem first_row_fixed : ∀ j : Fin 6, mixedHit 1 j = false := by
  decide +kernel

theorem centralGenerator_mem_center : rows 1 ∈ Subgroup.center Original := by
  apply (mem_center_iff_generator_commute ambient (closureGenerators_full g) _).mpr
  intro j
  apply commutatorElement_eq_one_iff_mul_comm.mp
  simpa only [first_row_fixed j, Bool.false_eq_true, ↓reduceIte] using rows_mixed 1 j

theorem Z_le_center : Z ≤ Subgroup.center Original := by
  apply (Subgroup.closure_le (Subgroup.center Original)).mpr
  rintro _ ⟨j, rfl⟩
  exact centralGenerator_mem_center

instance Z_normal : Z.Normal where
  conj_mem x hx y := by
    have hc := Subgroup.mem_center_iff.mp (Z_le_center hx) y
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    exact hx

theorem rows_full : Subgroup.closure (Set.range rows) = R := by
  apply le_antisymm
  · apply (Subgroup.closure_le R).mpr
    rintro _ ⟨i, rfl⟩
    exact BinaryCarrierDerivedRadical16T1547.elements_mem_radical i
  · intro x hx
    obtain ⟨i, hi⟩ := saturation.rows_cover x hx
    change rows i = x at hi
    rw [← hi]
    exact Subgroup.subset_closure (Set.mem_range_self i)

theorem radical_le_Z : primeRelativeRadical 2 R ≤ Z := by
  apply primeRelativeRadical_le_of_finite_generator_tests 2 R
    ambient (closureGenerators_full g) rows rows_full Z
  · intro i
    rw [rows_square]
    exact Z.one_mem
  · intro i j
    rw [rows_mixed]
    split
    · exact Subgroup.subset_closure (Set.mem_range_self (0 : Fin 1))
    · exact Z.one_mem

theorem Z_le_mixed : Z ≤ ⁅R, (⊤ : Subgroup Original)⁆ := by
  apply (Subgroup.closure_le ⁅R, (⊤ : Subgroup Original)⁆).mpr
  rintro _ ⟨j, rfl⟩
  have hm := Subgroup.commutator_mem_commutator
    (BinaryCarrierDerivedRadical16T1547.elements_mem_radical 2)
    (Subgroup.mem_top (ambient 4))
  have he := rows_mixed 2 4
  change ⁅rows 2, ambient 4⁆ = rows 1 at he
  rw [he] at hm
  exact hm

theorem relativeRadical_eq_Z : primeRelativeRadical 2 R = Z := by
  apply le_antisymm radical_le_Z
  exact Z_le_mixed.trans
    ((primeRelativePowerCommutator_commutator_le 2 R).trans
      (primeRelativePowerCommutator_le_radical 2 R))

theorem mixed_eq_Z : ⁅R, (⊤ : Subgroup Original)⁆ = Z := by
  apply le_antisymm _ Z_le_mixed
  exact ((primeRelativePowerCommutator_commutator_le 2 R).trans
    (primeRelativePowerCommutator_le_radical 2 R)).trans radical_le_Z

theorem normal_comparable (M : Subgroup Original) [M.Normal] (hM : M ≤ R) :
    M ≤ Z ∨ Z ≤ M := saturation.comparable M hM

/-- This is the exact radical for every original normal subgroup above
Z inside R. No intrinsic character space of R or M is substituted. -/
theorem relativeRadical_eq_Z_of_not_le (M : Subgroup Original) [M.Normal]
    (hM : M ≤ R) (hnot : ¬ M ≤ Z) : primeRelativeRadical 2 M = Z := by
  apply le_antisymm
  · exact (primeRelativeRadical_mono 2 M R hM).trans radical_le_Z
  · exact (saturation.radical_le_commutator
      BinaryCarrierRadicalHead16T1547.nonempty_words M hM hnot).trans
      ((primeRelativePowerCommutator_commutator_le 2 M).trans
        (primeRelativePowerCommutator_le_radical 2 M))

theorem mixed_eq_Z_of_not_le (M : Subgroup Original) [M.Normal]
    (hM : M ≤ R) (hnot : ¬ M ≤ Z) : ⁅M, (⊤ : Subgroup Original)⁆ = Z := by
  apply le_antisymm
  · exact (Subgroup.commutator_mono hM le_rfl).trans mixed_eq_Z.le
  · exact saturation.radical_le_commutator
      BinaryCarrierRadicalHead16T1547.nonempty_words M hM hnot

theorem card_eq_pow_head_mul_two (M : Subgroup Original) [M.Normal]
    (hM : M ≤ R) (hnot : ¬ M ≤ Z) :
    Nat.card M = 2 ^ Module.finrank (ZMod 2) (primeRelativeCharacters 2 M) * 2 := by
  have h := primeRelativeRadical_card_factorization 2 M
  rw [relativeRadical_eq_Z_of_not_le M hM hnot,
    BinaryCarrierRadicalHead16T1547.card_Z] at h
  exact h

end SymmetricSubgroupAsymptotics.BinaryCarrierRadicalStructure16T1547
