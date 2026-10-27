import SymmetricSubgroupAsymptotics.TenPointHalfDegreeFiniteModelReduction
import SymmetricSubgroupAsymptotics.TenPointGlobalCounterexampleCompleteCFSG

/-! All subgroups through degree10 satisfy the half-degree bound, apart
from the actual natural S3 exception. The independently closed global
counterexample supplies the finite reduction internally. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TenPointHalfDegreeCompleteCFSG

theorem subgroup_half_degree (hCFSG : CFSG.CFSGClassification) (n : ℕ) (hn : n ≤ 10)
    (J : Subgroup (Equiv.Perm (Fin n))) (hthree : n=3 → J≠⊤) :
    2*MarkedC4.genRank J ≤ n := by
  rcases TenPointHalfDegreeFiniteModelReduction.half_degree_or_sporadic_counterexample
    hCFSG n hn J hthree with hpaid | hbad
  · exact hpaid
  · exact (TenPointGlobalCounterexampleCompleteCFSG.no_primitive_sporadic_counterexample_ten
      hCFSG (EightPointFaithfulActionHalfDegreeReduction.counterexample_mono hn hbad)).elim

theorem faithful_half_degree (hCFSG : CFSG.CFSGClassification)
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (hsmall : Nat.card X ≤ 10) (hthree : Nat.card X≠3) :
    2*MarkedC4.genRank G ≤ Nat.card X := by
  rcases TenPointHalfDegreeFiniteModelReduction.two_mul_genRank_le_card_or_sporadic_counterexample
    (G := G) (X := X) hCFSG hsmall hthree with hpaid | hbad
  · exact hpaid
  · exact (TenPointGlobalCounterexampleCompleteCFSG.no_primitive_sporadic_counterexample_ten
      hCFSG hbad).elim

def fixedBudget (m : ℕ) : ℕ := if m=3 then 2 else m/2

theorem subgroup_genRank_le_fixedBudget (hCFSG : CFSG.CFSGClassification)
    (n : ℕ) (hn : n ≤ 10) (J : Subgroup (Equiv.Perm (Fin n))) :
    MarkedC4.genRank J ≤ fixedBudget n := by
  by_cases h3 : n=3
  · subst n
    have hc : Nat.card J ≤ 6 := by
      simpa only [Nat.card_perm,Nat.card_fin] using
        Nat.card_le_card_of_injective (Subtype.val : J → Equiv.Perm (Fin 3))
          Subtype.val_injective
    have hr : MarkedC4.genRank J ≤ 2 := by
      by_contra hh
      have hp := (Nat.pow_le_pow_right (by decide : 0 < 2)
        (show 3 ≤ MarkedC4.genRank J by omega)).trans
        ((FiniteGroupBinaryOrderGenerators.two_pow_genRank_le_card J).trans hc)
      norm_num at hp
    simpa only [fixedBudget,if_pos rfl] using hr
  · have hh := subgroup_half_degree hCFSG n hn J (fun h => (h3 h).elim)
    have hr : MarkedC4.genRank J ≤ n/2 := by omega
    simpa only [fixedBudget,if_neg h3] using hr

theorem faithful_genRank_le_fixedBudget (hCFSG : CFSG.CFSGClassification)
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (hsmall : Nat.card X ≤ 10) : MarkedC4.genRank G ≤ fixedBudget (Nat.card X) := by
  let points : X ≃ Fin (Nat.card X) := Finite.equivFinOfCardEq rfl
  exact (CoprimeNilpotentProductGenerators.genRank_mulEquiv
    (faithfulLabelledActionEquiv points)).le.trans
    (subgroup_genRank_le_fixedBudget hCFSG (Nat.card X) hsmall
      (labelledActionImage (A := G) points))

theorem ten_genRank_le_five (hCFSG : CFSG.CFSGClassification)
    (J : Subgroup (Equiv.Perm (Fin 10))) : MarkedC4.genRank J ≤ 5 := by
  simpa only [fixedBudget,if_neg (by decide : (10 : ℕ)≠3),Nat.reduceDiv] using
    subgroup_genRank_le_fixedBudget hCFSG 10 (by decide) J

end SymmetricSubgroupAsymptotics.TenPointHalfDegreeCompleteCFSG
