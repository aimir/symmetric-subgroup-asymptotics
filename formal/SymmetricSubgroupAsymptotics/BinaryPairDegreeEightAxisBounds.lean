import SymmetricSubgroupAsymptotics.BinaryPairDegreeEightAxisModels

/-! Uniform actual-intersection head ceilings at the two literal eight-
point tops. These bounds come from the complete checked natural-module
registries, including the original correlated subspace itself. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U (Fin 8)) (hU : IsPGroup 2 U)
  (B : Subgroup U) [B.Normal] (hB : B ≤ F.top.ker)
include hU hB

theorem regular_axis_normalGen_le
    (hH : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T3.generators)) :
    MarkedC4.normalGen B ≤ 3 := by
  let W := F.literalTopAxis BinaryRegularEightNaturalRegistry.H hH B
  have hh : MarkedC4.normalGen B =
      Module.finrank (ZMod 2) W.toRepresentation.Coinvariants :=
    (F.axis_normalGen_eq_coinvariants B hB hU).trans
      (F.literalTopAxis_head BinaryRegularEightNaturalRegistry.H hH B).symm
  obtain ⟨i, hi⟩ := BinaryRegularEightNaturalRegistry.complete W
  have hb := BinaryRegularEightNaturalRegistry.coinvariants_finrank_le i
  have hc : ∀ j : Fin 47, BinaryRegularEightNaturalRegistry.headCeiling j ≤ 3 := by decide +kernel
  rw [hi] at hb
  exact hh.le.trans (hb.trans (hc i))

theorem heisenberg_axis_normalGen_le
    (hH : F.top.range = Subgroup.closure (Set.range BinaryMenuCayley8T22.generators)) :
    MarkedC4.normalGen B ≤ 2 := by
  let W := F.literalTopAxis BinaryHeisenbergEightNaturalHeads.H hH B
  have hh : MarkedC4.normalGen B =
      Module.finrank (ZMod 2) W.toRepresentation.Coinvariants :=
    (F.axis_normalGen_eq_coinvariants B hB hU).trans
      (F.literalTopAxis_head BinaryHeisenbergEightNaturalHeads.H hH B).symm
  obtain ⟨i, hi⟩ := BinaryHeisenbergEightNaturalHeads.complete W
  have hb := BinaryHeisenbergEightNaturalHeads.coinvariants_finrank_le i
  have hc : ∀ j : Fin 15, BinaryHeisenbergEightNaturalHeads.headCeiling j ≤ 2 := by decide +kernel
  rw [hi] at hb
  exact hh.le.trans (hb.trans (hc i))

end SymmetricSubgroupAsymptotics.BinaryPairFrame
