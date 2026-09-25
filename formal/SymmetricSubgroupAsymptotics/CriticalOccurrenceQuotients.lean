import SymmetricSubgroupAsymptotics.CriticalProductTransport

/-! Binary quotients of every original occurrence, including unsplit V4 blocks. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

def criticalLocalRank : CriticalActionKind → ℕ
  | .c2 => 1 | .v4 => 2 | .d8 => 2 | .e8 => 4

def criticalLocalQuotient (i : CriticalActionKind) :
    CriticalLocalGroup i →* Multiplicative (Fin (criticalLocalRank i) → ZMod 2) := by
  cases i
  · exact MonoidHom.id _
  · exact MonoidHom.id _
  · exact (AddMonoidHom.toMultiplicative d8QuotientChart.toLinearMap.toAddMonoidHom).comp
      (BinaryHeisenberg.quotient 1)
  · exact (AddMonoidHom.toMultiplicative e8QuotientChart.toLinearMap.toAddMonoidHom).comp
      (BinaryHeisenberg.quotient 2)

theorem criticalLocalQuotient_surjective (i : CriticalActionKind) :
    Function.Surjective (criticalLocalQuotient i) := by
  cases i
  · exact Function.surjective_id
  · exact Function.surjective_id
  · intro v
    exact ⟨⟨(d8QuotientChart.symm v.toAdd).1, (d8QuotientChart.symm v.toAdd).2, 0⟩,
      congrArg Multiplicative.ofAdd (d8QuotientChart.apply_symm_apply v.toAdd)⟩
  · intro v
    exact ⟨⟨(e8QuotientChart.symm v.toAdd).1, (e8QuotientChart.symm v.toAdd).2, 0⟩,
      congrArg Multiplicative.ofAdd (e8QuotientChart.apply_symm_apply v.toAdd)⟩

theorem criticalLocalQuotient_d8_eq_one (g : BinaryHeisenberg 1) :
    criticalLocalQuotient .d8 g = 1 ↔ g.a = 0 ∧ g.b = 0 := by
  change d8QuotientChart (g.a, g.b) = 0 ↔ _
  constructor
  · intro h
    exact Prod.mk.inj (d8QuotientChart.injective (h.trans d8QuotientChart.map_zero.symm))
  · rintro ⟨ha, hb⟩
    simp [ha, hb]

theorem criticalLocalQuotient_e8_eq_one (g : BinaryHeisenberg 2) :
    criticalLocalQuotient .e8 g = 1 ↔ g.a = 0 ∧ g.b = 0 := by
  change e8QuotientChart (g.a, g.b) = 0 ↔ _
  constructor
  · intro h
    exact Prod.mk.inj (e8QuotientChart.injective (h.trans e8QuotientChart.map_zero.symm))
  · rintro ⟨ha, hb⟩
    simp [ha, hb]

abbrev CriticalProfileOccurrence (p : CriticalProfile) :=
  (i : CriticalActionKind) × Fin (p.multiplicity i)

def criticalOccurrenceRank (p : CriticalProfile) (x : CriticalProfileOccurrence p) : ℕ :=
  criticalLocalRank x.1

abbrev CriticalOccurrenceGroup (p : CriticalProfile) (x : CriticalProfileOccurrence p) : Type :=
  criticalActionSubgroup x.1

def criticalOccurrenceQuotient (p : CriticalProfile) (x : CriticalProfileOccurrence p) :
    CriticalOccurrenceGroup p x →* Multiplicative (Fin (criticalOccurrenceRank p x) → ZMod 2) :=
  (criticalLocalQuotient x.1).comp (criticalLocalEquiv x.1).symm.toMonoidHom

theorem criticalOccurrenceQuotient_surjective (p : CriticalProfile) (x : CriticalProfileOccurrence p) :
    Function.Surjective (criticalOccurrenceQuotient p x) :=
  (criticalLocalQuotient_surjective x.1).comp (criticalLocalEquiv x.1).symm.surjective

/-- Flattening occurrence indices changes no local group coordinate. -/
def criticalProfileOccurrenceEquiv (p : CriticalProfile) :
    OrbitProfileProductGroup p.multiplicity criticalActionSubgroup ≃*
      (∀ x : CriticalProfileOccurrence p, CriticalOccurrenceGroup p x) where
  toFun g x := g x.1 x.2
  invFun g i j := g ⟨i, j⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private theorem criticalKind_univ : (Finset.univ : Finset CriticalActionKind) =
    {.c2, .v4, .d8, .e8} := by decide

theorem criticalOccurrenceRank_sum (p : CriticalProfile) :
    ∑ x : CriticalProfileOccurrence p, criticalOccurrenceRank p x = p.rank := by
  simp only [criticalOccurrenceRank, Fintype.sum_sigma, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, criticalKind_univ]
  simp [CriticalProfile.multiplicity, criticalLocalRank, CriticalProfile.rank]
  omega

theorem criticalOccurrenceRank_bounds (p : CriticalProfile) (x : CriticalProfileOccurrence p) :
    1 ≤ criticalOccurrenceRank p x ∧ criticalOccurrenceRank p x ≤ 4 := by
  rcases x with ⟨i,j⟩
  cases i <;> norm_num [criticalOccurrenceRank, criticalLocalRank]

theorem criticalOccurrence_card_le_rank (p : CriticalProfile) :
    Fintype.card (CriticalProfileOccurrence p) ≤ p.rank := by
  rw [← criticalOccurrenceRank_sum]
  simpa using Finset.sum_le_sum (s := Finset.univ)
    (fun x _ ↦ (criticalOccurrenceRank_bounds p x).1)

/-- The two independently constructed quotient charts retain exactly the
same original kernel, coordinate by coordinate. -/
theorem criticalProfileProductEquiv_mem_kernel_iff (p : CriticalProfile)
    (g : OrbitProfileProductGroup p.multiplicity criticalActionSubgroup) :
    criticalProfileProductEquiv p g ∈
      (criticalProductQuotient p.abelianRank (criticalProfileNonabelianChoice p)).ker ↔
    ∀ x : CriticalProfileOccurrence p,
      criticalOccurrenceQuotient p x (criticalProfileOccurrenceEquiv p g x) = 1 := by
  rw [mem_criticalProductQuotient_ker]
  constructor
  · rintro ⟨hw, hi⟩ ⟨i,j⟩
    have hw' := congrArg (fun w ↦ criticalProfileAbelianChart p w.toAdd) hw
    have hf :
        ((fun j ↦ ((criticalLocalEquiv .c2).symm (g .c2 j)).toAdd,
         fun j ↦ ((criticalLocalEquiv .v4).symm (g .v4 j)).toAdd) : CriticalProfileAbelianSpace p) = 0 := by
      simpa [criticalProfileProductEquiv] using hw'
    cases i
    · exact Multiplicative.toAdd.injective (congrFun (congrArg Prod.fst hf) j)
    · exact Multiplicative.toAdd.injective (congrFun (congrArg Prod.snd hf) j)
    · apply (criticalLocalQuotient_d8_eq_one _).mpr
      exact hi (.inl j)
    · apply (criticalLocalQuotient_e8_eq_one _).mpr
      exact hi (.inr j)
  · intro h
    constructor
    · apply Multiplicative.toAdd.injective
      change (criticalProfileAbelianChart p).symm _ = 0
      rw [← (criticalProfileAbelianChart p).symm.map_zero]
      apply congrArg (criticalProfileAbelianChart p).symm
      apply Prod.ext
      · funext j
        exact congrArg Multiplicative.toAdd (h ⟨.c2,j⟩)
      · funext j
        exact congrArg Multiplicative.toAdd (h ⟨.v4,j⟩)
    · intro i
      cases i with
      | inl j => exact (criticalLocalQuotient_d8_eq_one _).mp (h ⟨.d8,j⟩)
      | inr j => exact (criticalLocalQuotient_e8_eq_one _).mp (h ⟨.e8,j⟩)

end SymmetricSubgroupAsymptotics
