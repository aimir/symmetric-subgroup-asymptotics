import SymmetricSubgroupAsymptotics.TraceyOrdinaryFourSporadicResidual
import SymmetricSubgroupAsymptotics.PrimitiveSocleYSectionSmallActionExclusion

/-! Actual Y degree27 eliminates the three small Y rows of the coarse
residual. The numerical callback and SAME original primitive/block
witness remain; only Monster survives this specific residual. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TraceyOrdinaryMonsterOnlyResidual
open PrimitiveSocleRawStructure TraceyStrictlySmallerTransitiveActions CFSGReduction
open PrimitiveSocleYSectionOrdinaryTail

private theorem monster_of_remaining (s : CFSG.Sporadic)
    (hs : CFSGGeneration.SporadicGenerationResidual s) (hj4 : s≠.j4)
    (h23 : s≠.fi23) (hY : ¬IsYSectionModel s) : s=.monster := by
  cases s <;> simp_all [CFSGGeneration.SporadicGenerationResidual,IsYSectionModel]

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)]

def ActualResidual : Prop :=
  (MulAction.IsPreprimitive J (Fin n) ∧
    ∃ D : NonaffineData J (Fin n), D.factorCount=1 ∧
      Nonempty (D.Simple ≃* CFSG.Sporadic.monster.Model)) ∨
  (¬MulAction.IsPreprimitive J (Fin n) ∧
    ∃ x₀ : Fin n, ∃ block : OriginalMinimalBlock (A := J) x₀,
      ∃ D : NonaffineData block.Component block.Fibre, Nat.card block.Fibre<32 ∧
        Nonempty (D.Simple ≃* CFSG.Sporadic.monster.Model))

theorem refine_actual_residual
    (h : TraceyOrdinaryFourSporadicResidual.ActualResidual J) : ActualResidual J := by
  rcases h with ⟨hp,D,hk,s,hs,⟨e⟩,hj4,h23,hY⟩ |
    ⟨hp,x₀,block,D,hlocal,s,hs,⟨e⟩,hj4,h23,hY⟩
  · have hnotY : ¬IsYSectionModel s := by
      intro hy
      have hd := PrimitiveSocleYSectionSmallActionExclusion.degree_ge_twentySeven D s hy e
      have hb := hY hy
      simp only [Nat.card_fin] at hd
      omega
    have he := monster_of_remaining s hs hj4 h23 hnotY
    subst s
    exact Or.inl ⟨hp,D,hk,⟨e⟩⟩
  · have hnotY : ¬IsYSectionModel s := by
      intro hy
      have hd := PrimitiveSocleYSectionSmallActionExclusion.degree_ge_twentySeven D s hy e
      have hb := hY hy
      omega
    have he := monster_of_remaining s hs hj4 h23 hnotY
    subst s
    exact Or.inr ⟨hp,x₀,block,D,hlocal,⟨e⟩⟩

variable
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingSufficientSimpleIndexAfterTits i →
        ModelBoundsAfterTitsIndexSquare i)

include remaining in
theorem actual_residual_of_failed_coarse
    (hCFSG : CFSG.CFSGClassification) (hn : 2≤n)
    (hbad : traceyPermutationGeneratorCeiling n<MarkedC4.genRank J)
    (hbelow : SmallerTransitiveRankBound n) : ActualResidual J :=
  refine_actual_residual J
    (TraceyOrdinaryFourSporadicResidual.actual_residual_of_failed_coarse
      remaining J hCFSG hn hbad hbelow)

include remaining in
theorem traceyPermutation_or_actual_minimal_monster_residual
    (hCFSG : CFSG.CFSGClassification) :
    TraceyPermutationGeneratorInput ∨
      ∃ n : ℕ, 2≤n ∧ ∃ J : Subgroup (Equiv.Perm (Fin n)),
        ∃ ht : MulAction.IsPretransitive J (Fin n),
          letI := ht
          traceyPermutationGeneratorCeiling n<MarkedC4.genRank J ∧
          SmallerTransitiveRankBound n ∧ ActualResidual J := by
  rcases TraceyOrdinaryFourSporadicResidual.traceyPermutation_or_actual_minimal_four_sporadic_residual
    remaining hCFSG with h | ⟨m,hm,L,ht,hbad,hbelow,hr⟩
  · exact Or.inl h
  · letI := ht
    exact Or.inr ⟨m,hm,L,ht,hbad,hbelow,refine_actual_residual L hr⟩

end SymmetricSubgroupAsymptotics.TraceyOrdinaryMonsterOnlyResidual
