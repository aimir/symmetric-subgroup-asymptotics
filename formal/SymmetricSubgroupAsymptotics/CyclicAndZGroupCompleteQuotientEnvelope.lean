import SymmetricSubgroupAsymptotics.SquarefreeGroupSocleOne
import SymmetricSubgroupAsymptotics.Non2PreE7SaprimOddCyclicAffine
import SymmetricSubgroupAsymptotics.GrowingQuotientTransferNumerics

/-! Complete literal normal-axis envelopes for cyclic groups and Z-groups.
The coefficient includes every original normal subgroup and every quotient
automorphism. Thus a socle-one assertion is applied separately to the actual
quotients, rather than incorrectly to the complete weight as a whole. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
attribute [-instance] SymmetricSubgroupAsymptotics.originalNormalFintype
attribute [local instance] Fintype.ofFinite
namespace SymmetricSubgroupAsymptotics.CyclicAndZGroupCompleteQuotientEnvelope

abbrev NormalAxis (G : Type) [Group G] := {N : Subgroup G // N.Normal}

def automorphismMass (G : Type) [Group G] [Finite G] : ℝ :=
  ∑ N : NormalAxis G, (Nat.card ((G ⧸ N.1) ≃* (G ⧸ N.1)) : ℝ)

variable {G : Type} [Group G] [Finite G]

theorem cyclic_complete_weight_le [IsCyclic G]
    (hKP : KovacsPraegerAbelianizationBound) {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := G) J ≤
      (Nat.card (NormalAxis G) : ℝ) *
        (2 : ℝ) ^ ((Real.logb 2 3 / 3) * (b : ℝ)) := by
  have haxis (N : NormalAxis G) :
      (Nat.card (GroupEpimorphism J (G ⧸ N.1)) : ℝ) ≤
        (2 : ℝ) ^ ((Real.logb 2 3 / 3) * (b : ℝ)) := by
    letI : N.1.Normal := N.2
    letI : IsCyclic (G ⧸ N.1) :=
      isCyclic_of_surjective (QuotientGroup.mk' N.1)
        (QuotientGroup.mk'_surjective N.1)
    have he : (Nat.card (GroupEpimorphism J (G ⧸ N.1)) : ℝ) ≤
        Nat.card (Abelianization J) := by
      exact_mod_cast cyclicGroupEpimorphism_card_le_abelianization
        (J := J) (Q := G ⧸ N.1) inferInstance
    exact (he.trans (hKP b J)).trans_eq (three_rpow_third_eq b)
  unfold completeQuotientWeight completeQuotientCount
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ _N : NormalAxis G,
        (2 : ℝ) ^ ((Real.logb 2 3 / 3) * (b : ℝ)) :=
      Finset.sum_le_sum (fun N _ => haxis N)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
        Fintype.card_eq_nat_card]

theorem zGroup_complete_weight_le [IsZGroup G]
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := G) J ≤ automorphismMass G *
      (2 : ℝ) ^ ((Real.logb 2 5 / 3) * (b : ℝ)) := by
  have haxis (N : NormalAxis G) :
      (Nat.card (GroupEpimorphism J (G ⧸ N.1)) : ℝ) ≤
        (Nat.card ((G ⧸ N.1) ≃* (G ⧸ N.1)) : ℝ) *
          (2 : ℝ) ^ ((Real.logb 2 5 / 3) * (b : ℝ)) := by
    letI : N.1.Normal := N.2
    letI : IsZGroup (G ⧸ N.1) :=
      IsZGroup.of_surjective (f := QuotientGroup.mk' N.1)
        (QuotientGroup.mk'_surjective N.1)
    have he := (hZmud.generalCertificate
      (socleNormalGeneratorBound_one_of_isZGroup (G := G ⧸ N.1))).envelope lit b J
    simpa only [ZmudFaithfulCharacterTupleInput.generalCertificate_slope,
      Nat.cast_one,one_mul] using he
  unfold completeQuotientWeight completeQuotientCount
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ N : NormalAxis G,
        (Nat.card ((G ⧸ N.1) ≃* (G ⧸ N.1)) : ℝ) *
          (2 : ℝ) ^ ((Real.logb 2 5 / 3) * (b : ℝ)) :=
      Finset.sum_le_sum (fun N _ => haxis N)
    _ = _ := by
      rw [←Finset.sum_mul]
      apply congrArg (fun z : ℝ => z * (2 : ℝ)^((Real.logb 2 5 / 3)*(b : ℝ)))
      unfold automorphismMass
      exact Finset.sum_congr (by ext N; simp) (fun _ _ => rfl)

theorem orderTen_complete_weight_le (hG : Nat.card G = 10)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := G) J ≤ automorphismMass G *
      (2 : ℝ) ^ ((Real.logb 2 5 / 3) * (b : ℝ)) := by
  letI : IsZGroup G := IsZGroup.of_squarefree (by rw [hG]; decide +kernel)
  exact zGroup_complete_weight_le hZmud lit J

end SymmetricSubgroupAsymptotics.CyclicAndZGroupCompleteQuotientEnvelope
