import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryCharts

/-! One selected, point-separating four-space:64 point pairs, tested
against four actual basis vectors. No permutation/group table is generated. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryRegularFourSpaceSeparates

private theorem basis_separates : ∀ x y : Fin 8,
    (∀ j : Fin 4,
      BinaryRegularEightNaturalRegistry.chart46.inclusion (Pi.single j 1) x=
        BinaryRegularEightNaturalRegistry.chart46.inclusion (Pi.single j 1) y) → x=y := by
  decide +kernel

theorem separates (x y : Fin 8)
    (h : ∀ v : Fin 8 → ZMod 2,v∈BinaryRegularEightNaturalRegistry.chart46.space → v x=v y) :
    x=y := by
  apply basis_separates x y
  intro j
  exact h _ (show _ ∈ BinaryRegularEightNaturalRegistry.chart46.inclusion.range from ⟨Pi.single j 1,rfl⟩)

end SymmetricSubgroupAsymptotics.BinaryRegularFourSpaceSeparates
