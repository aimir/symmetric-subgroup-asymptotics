import SymmetricSubgroupAsymptotics.CFSGAffineCoarseComposition
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawONanScottProof

/-! Unconditional coarse bounds for the actual soluble primitive action.
The nonaffine alternative is impossible because its actual socle has a
nonabelian simple quotient. No quantitative published input is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSolublePrimitiveCoarse
open PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X] [IsSolvable G]

theorem affineProfile : Nonempty (PrimitiveAffineProfile G X) := by
  obtain ⟨D | P⟩ := publishedONanScottStructure G X
  · let i : Fin D.factorCount := ⟨0, D.factorCount_pos⟩
    let f : finiteGroupSocle G →* D.Simple :=
      (Pi.evalMonoidHom (fun _ : Fin D.factorCount => D.Simple) i).comp D.socleEquiv.toMonoidHom
    have hf : Function.Surjective f := by
      intro t
      exact ⟨D.socleEquiv.symm (fun _ => t), by simp [f]⟩
    letI : IsSolvable D.Simple := solvable_of_surjective (f := f) hf
    exact False.elim (D.noncommutative (isMulCommutative_iff.mpr
      (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance)))
  · exact ⟨P⟩

private theorem floor_bound :
    (1 + (Nat.log 2 (Nat.card X) : ℝ)) * Real.logb 2 (Nat.card X) ≤
      (Real.logb 2 (Nat.card X))^2 + Real.logb 2 (Nat.card X) := by
  have hfloor := Real.natLog_le_logb (Nat.card X) 2
  change (Nat.log 2 (Nat.card X) : ℝ) ≤ Real.logb 2 (Nat.card X) at hfloor
  have hL : 0 ≤ Real.logb 2 (Nat.card X) :=
    Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (by exact_mod_cast (Nat.card_pos (α := X)))
  nlinarith [mul_le_mul_of_nonneg_right hfloor hL]

theorem composition_length (s : SubnormalCompositionSeries G) :
    (s.chain.length : ℝ) ≤ (Real.logb 2 (Nat.card X))^2 + Real.logb 2 (Nat.card X) := by
  obtain ⟨P⟩ := affineProfile (G := G) (X := X)
  exact (CFSGAffineCoarseComposition.composition_length_le_domain_log P
    (Classical.arbitrary X) s).trans (floor_bound (X := X))

theorem subgroup_rank (N : Subgroup G) :
    (Group.rank N : ℝ) ≤ (Real.logb 2 (Nat.card X))^2 + Real.logb 2 (Nat.card X) := by
  obtain ⟨P⟩ := affineProfile (G := G) (X := X)
  exact (CFSGAffineCoarseComposition.subgroup_rank_le_domain_log P
    (Classical.arbitrary X) N).trans (floor_bound (X := X))

end SymmetricSubgroupAsymptotics.CFSGSolublePrimitiveCoarse
