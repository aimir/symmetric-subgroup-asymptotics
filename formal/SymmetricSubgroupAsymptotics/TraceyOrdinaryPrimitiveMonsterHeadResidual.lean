import SymmetricSubgroupAsymptotics.TraceyOrdinaryFiniteMonsterResidual
import SymmetricSubgroupAsymptotics.PrimitiveSocleMonsterRemoteTailDegree

/-! The actual index33 excludes every original Monster block fibre27..31.
Only the fixed bounded primitive Monster head remains. The cutoff is
selected before the minimal bad group by the existing fixed-model tail;
this is not a proof of that finite primitive head or of full Tracey. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TraceyOrdinaryPrimitiveMonsterHeadResidual
open PrimitiveSocleRawStructure CFSGReduction TraceyStrictlySmallerTransitiveActions
variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)]

def ActualPrimitiveHead (N : ℕ) : Prop :=
  MulAction.IsPreprimitive J (Fin n) ∧ 33 ≤ n ∧ n < N ∧
    ∃ D : NonaffineData J (Fin n), D.factorCount=1 ∧
      Nonempty (D.Simple ≃* CFSG.Sporadic.monster.Model)

theorem refine_actual_residual (N : ℕ)
    (h : TraceyOrdinaryFiniteMonsterResidual.ActualResidual J N) : ActualPrimitiveHead J N := by
  rcases h with ⟨hp,_h27,hN,D,hk,⟨e⟩⟩ | ⟨_hp,x₀,block,D,_h27,hsmall,⟨e⟩⟩
  · have hd := PrimitiveSocleMonsterRemoteTailDegree.degree_ge_thirtyThree D e
    simp only [Nat.card_fin] at hd
    exact ⟨hp,hd,hN,D,hk,⟨e⟩⟩
  · have hd := PrimitiveSocleMonsterRemoteTailDegree.degree_ge_thirtyThree D e
    omega

variable
    (remaining : ∀ (i : CFSG.Index) [Finite i.Model] [IsSimpleGroup i.Model],
      ¬IsMulCommutative i.Model → RemainingSufficientSimpleIndexAfterTits i →
        ModelBoundsAfterTitsIndexSquare i)

include remaining in
theorem traceyPermutation_or_bounded_primitive_monster_head
    (hCFSG : CFSG.CFSGClassification) :
    ∃ N : ℕ, TraceyPermutationGeneratorInput ∨
      ∃ m : ℕ, 2 ≤ m ∧ ∃ L : Subgroup (Equiv.Perm (Fin m)),
        ∃ ht : MulAction.IsPretransitive L (Fin m),
          letI := ht
          traceyPermutationGeneratorCeiling m < MarkedC4.genRank L ∧
            SmallerTransitiveRankBound m ∧ ActualPrimitiveHead L N := by
  obtain ⟨N,hN⟩ := TraceyOrdinaryFiniteMonsterResidual.traceyPermutation_or_bounded_actual_monster_residual remaining hCFSG
  refine ⟨N,?_⟩
  rcases hN with hpaid | ⟨m,hm,L,ht,hbad,hbelow,hr⟩
  · exact Or.inl hpaid
  · letI := ht
    exact Or.inr ⟨m,hm,L,ht,hbad,hbelow,refine_actual_residual L N hr⟩

end SymmetricSubgroupAsymptotics.TraceyOrdinaryPrimitiveMonsterHeadResidual
