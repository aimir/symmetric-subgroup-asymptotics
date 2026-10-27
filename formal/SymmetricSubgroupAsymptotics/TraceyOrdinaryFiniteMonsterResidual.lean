import SymmetricSubgroupAsymptotics.TraceyOrdinaryMonsterOnlyResidual
import SymmetricSubgroupAsymptotics.PrimitiveSocleMonsterSmallActionExclusion
import SymmetricSubgroupAsymptotics.FiniteModelOneFactorOrdinaryTail

/-! The remaining original coarse counterexample has either a bounded
primitive Monster degree, or an actual Monster block of degree27..31.
The primitive cutoff is constructed internally from a fixed-model tail;
no displayed Monster generators, model order, or extra callback is used.
This is a residual theorem, not the full coarse generation bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TraceyOrdinaryFiniteMonsterResidual
open PrimitiveSocleRawStructure CFSGReduction TraceyStrictlySmallerTransitiveActions
variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)]

def ActualResidual (N : ℕ) : Prop :=
  (MulAction.IsPreprimitive J (Fin n) ∧ 27 ≤ n ∧ n < N ∧
    ∃ D : NonaffineData J (Fin n), D.factorCount = 1 ∧
      Nonempty (D.Simple ≃* CFSG.Sporadic.monster.Model)) ∨
  (¬MulAction.IsPreprimitive J (Fin n) ∧
    ∃ x₀ : Fin n, ∃ block : OriginalMinimalBlock (A := J) x₀,
      ∃ D : NonaffineData block.Component block.Fibre,
        27 ≤ Nat.card block.Fibre ∧ Nat.card block.Fibre < 32 ∧
          Nonempty (D.Simple ≃* CFSG.Sporadic.monster.Model))

theorem refine_actual_residual (N : ℕ)
    (hmodel : FiniteModelOneFactorOrdinaryTail.PaysOneFactorModel
      CFSG.Sporadic.monster.Model N)
    (hbad : traceyPermutationGeneratorCeiling n < MarkedC4.genRank J)
    (h : TraceyOrdinaryMonsterOnlyResidual.ActualResidual J) : ActualResidual J N := by
  rcases h with ⟨hp,D,hk,⟨e⟩⟩ | ⟨hp,x₀,block,D,hlocal,⟨e⟩⟩
  · have hd : 27 ≤ n := by
      simpa only [Nat.card_fin] using
        PrimitiveSocleMonsterSmallActionExclusion.degree_ge_twentySeven D e
    have hupper : n < N := by
      by_contra hn
      have hgen := hmodel D hk e (by simpa only [Nat.card_fin] using (show N ≤ n by omega))
      simp only [Nat.card_fin] at hgen
      omega
    exact Or.inl ⟨hp,hd,hupper,D,hk,⟨e⟩⟩
  · exact Or.inr ⟨hp,x₀,block,D,
      PrimitiveSocleMonsterSmallActionExclusion.degree_ge_twentySeven D e,hlocal,⟨e⟩⟩

variable
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingSufficientSimpleIndexAfterTits i →
        ModelBoundsAfterTitsIndexSquare i)

include remaining in
theorem traceyPermutation_or_bounded_actual_monster_residual
    (hCFSG : CFSG.CFSGClassification) :
    ∃ N : ℕ, TraceyPermutationGeneratorInput ∨
      ∃ m : ℕ, 2 ≤ m ∧ ∃ L : Subgroup (Equiv.Perm (Fin m)),
        ∃ ht : MulAction.IsPretransitive L (Fin m),
          letI := ht
          traceyPermutationGeneratorCeiling m < MarkedC4.genRank L ∧
            SmallerTransitiveRankBound m ∧ ActualResidual L N := by
  obtain ⟨N,hN⟩ := FiniteModelOneFactorOrdinaryTail.exists_threshold
    CFSG.Sporadic.monster.Model
  refine ⟨N,?_⟩
  rcases TraceyOrdinaryMonsterOnlyResidual.traceyPermutation_or_actual_minimal_monster_residual
    remaining hCFSG with hpaid | ⟨m,hm,L,ht,hbad,hbelow,hr⟩
  · exact Or.inl hpaid
  · letI := ht
    exact Or.inr ⟨m,hm,L,ht,hbad,hbelow,refine_actual_residual L N hN hbad hr⟩

end SymmetricSubgroupAsymptotics.TraceyOrdinaryFiniteMonsterResidual
