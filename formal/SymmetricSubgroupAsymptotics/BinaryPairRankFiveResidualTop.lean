import SymmetricSubgroupAsymptotics.BinaryPairSingleCyclicOrbitRankBound

/-! Rank five away from the two already recognized exceptional eight-point
 tops. This reduction retains the actual pair kernel and original top;
 it asserts no exponent condition or normal-F packet for the residual. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X]
    (F : BinaryPairFrame U (Fin 8)) [MulAction U (Fin 8)]
    (hact : ∀ (u : U) (i : Fin 8), u • i = F.top u i)

include hact

/-- Outside the two literal top templates, the entire rank-five source
 saturates the actual kernel/top generation inequality. The conclusion
 does not replace the arbitrary lift offsets or original kernel. -/
theorem rank_five_residual_top_saturation
    (hU : IsPGroup 2 U) (hrank : 5 ≤ MarkedC4.genRank U)
    (hregular : ¬ ∃ g : Equiv.Perm (Fin 8), MulAut.conj g • F.top.range =
      Subgroup.closure (Set.range BinaryMenuCayley8T3.generators))
    (hheisenberg : ¬ ∃ g : Equiv.Perm (Fin 8), MulAut.conj g • F.top.range =
      Subgroup.closure (Set.range BinaryMenuCayley8T22.generators)) :
    MarkedC4.genRank U = 5 ∧
    MarkedC4.normalGen F.top.ker = 2 ∧
    MarkedC4.genRank F.top.range = 3 ∧
    MarkedC4.genRank U = MarkedC4.normalGen F.top.ker + MarkedC4.genRank F.top.range ∧
    (∀ (A : Subgroup U) [A.Normal], A ≤ F.top.ker → MarkedC4.normalGen A ≤ 2) ∧
    ¬ ∃ g : U, Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers g) (Fin 8)) = 1 := by
  letI residualTop_pretransitive : MulAction.IsPretransitive F.top.range (Fin 8) :=
    F.top_pretransitive
  have htrans : ∀ i j : Fin 8, ∃ t : F.top.range, t.val i = j := by
    intro i j
    exact MulAction.exists_smul_eq F.top.range i j
  letI residualOriginal_pretransitive : MulAction.IsPretransitive U (Fin 8) := ⟨by
    intro i j
    obtain ⟨t, ht⟩ := htrans i j
    obtain ⟨u, rfl⟩ := F.top.rangeRestrict_surjective t
    exact ⟨u, (hact u i).trans ht⟩⟩
  have hTop := F.top_isPGroup hU
  have htop : MarkedC4.genRank F.top.range ≤ 3 := by
    by_contra hn
    have hf : 4 ≤ MarkedC4.genRank F.top.range := by omega
    exact hheisenberg
      (BinaryDegreeEightHighRankAction.four_le_genRank_action_conjugate_heisenberg
        F.top.range hTop htrans hf)
  have hnon : ¬ BinarySquareActionStructure.SquaresActTrivially
      (G := U) (X := Fin 8) := by
    intro hel
    apply hregular
    apply BinaryDegreeEightElementaryActionCoverage.elementary_action_conjugate_regular
      F.top.range hTop htrans
    intro t i
    obtain ⟨u, rfl⟩ := F.top.rangeRestrict_surjective t
    rw [← map_pow]
    exact (hact (u ^ 2) i).symm.trans (hel u i)
  have hall (A : Subgroup U) [A.Normal] (hA : A ≤ F.top.ker) :
      MarkedC4.normalGen A ≤ 2 := by
    simpa only [Nat.card_fin] using
      F.normalGen_le_quarter_of_not_elementary hact hU hnon A hA
  have hk := hall F.top.ker le_rfl
  have hadd := F.genRank_le_actual_pair_kernel_add_top
  have hu : MarkedC4.genRank U = 5 := by omega
  have hk' : MarkedC4.normalGen F.top.ker = 2 := by omega
  have ht' : MarkedC4.genRank F.top.range = 3 := by omega
  refine ⟨hu, hk', ht', by omega, hall, ?_⟩
  exact F.no_single_cyclic_orbit_of_rank_five hact hU hrank htop

end SymmetricSubgroupAsymptotics.BinaryPairFrame
