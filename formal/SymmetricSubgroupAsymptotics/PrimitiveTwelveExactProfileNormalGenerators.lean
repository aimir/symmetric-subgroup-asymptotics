import SymmetricSubgroupAsymptotics.PrimitiveSixExactProfileNormalGenerators
import SymmetricSubgroupAsymptotics.NormalChainSocleGenerators

/-! Degree12 from the existing exact primitive socle profile and existing
116-row bounded catalogue. Since5²>12 there is one socle factor; the six
stored degree12rows have outer order at most2. No new degree12 catalogue
or normal-subgroup list is introduced. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveTwelveExactProfileNormalGenerators

theorem twelve_not_two_power (d : ℕ) : 12≠2^d := by
  intro h
  by_cases hd : d<4
  · interval_cases d <;> norm_num at h
  · have h4 : 4≤d := by omega
    have h16 : (16 : ℕ)≤2^d := pow_le_pow_right₀ (by decide : (1 : ℕ)≤2) h4
    omega

/-- Kernel reduction inspects the existing displayed catalogue rows only. -/
theorem twelve_receipt_outer_le_two : ∀ i : Fin 116,
    (primitiveBoundedIndexRow i).degree=12 →
      (primitiveBoundedIndexRow i).outerOrder≤2 := by
  decide +kernel

variable {L : Type} [Group L] [Finite L] [MulAction L (Fin 12)]
    [FaithfulSMul L (Fin 12)] [MulAction.IsPreprimitive L (Fin 12)]
    (D : ExactPrimitiveSemisimpleOuterLogProfile L 12)
    (catalogue : PublishedBoundedPrimitiveCatalogueClassification)

theorem factorCount_eq_one : D.profile.factorCount=1 := by
  have hp := D.profile.factorCount_pos
  have h5 := D.profile.leastIndex_five_le
  have hl := D.profile.primitive_index_lower
  by_contra hn
  have h2 : 2≤D.profile.factorCount := by omega
  have h25 : 25≤D.profile.leastIndex^D.profile.factorCount := by
    calc
      25=(5 : ℕ)^2 := rfl
      _≤D.profile.leastIndex^2 := Nat.pow_le_pow_left h5 2
      _≤D.profile.leastIndex^D.profile.factorCount :=
        pow_le_pow_right₀ (by omega : 1≤D.profile.leastIndex) h2
  omega

include catalogue in
theorem socle_quotient_card_le_two : Nat.card (L ⧸ D.profile.E)≤2 := by
  have hone := factorCount_eq_one D
  obtain ⟨M⟩ := catalogue L (Fin 12) D.profile.E D.profile.chart
    (by simp) (by simp) (D.oneFactor_socle_nontrivial hone)
    (D.oneFactor_socle_le hone) (D.factorCount_eq_chart.symm.trans hone)
  exact M.quotientOrder_eq.trans_le
    (twelve_receipt_outer_le_two M.row (by simpa using M.degree_eq))

include D catalogue in
theorem normal_total (A B : Subgroup L) (hA : A.Normal) (hB : B.Normal) : A≤B ∨ B≤A :=
  PrimitiveSixExactProfileNormalGenerators.normal_total_of_unique_minimal_small_quotient
    D.profile.E (D.oneFactor_socle_le (factorCount_eq_one D))
    (socle_quotient_card_le_two D catalogue) A B hA hB

include D catalogue in
theorem normal_generating_singletons (N : Subgroup L) (hN : N.Normal) :
    ∃ x : Fin 1 → L, Subgroup.normalClosure (Set.range x)=N :=
  normal_generating_singletons_of_finite_normal_total (normal_total D catalogue) N hN

include D catalogue in
theorem quotientSocle_one (N : Subgroup L) [N.Normal] :
    SocleNormalGeneratorBound (L ⧸ N) 1 :=
  quotientSocleNormalGeneratorBound_one_of_normal_total (normal_total D catalogue) N

end SymmetricSubgroupAsymptotics.PrimitiveTwelveExactProfileNormalGenerators
end
