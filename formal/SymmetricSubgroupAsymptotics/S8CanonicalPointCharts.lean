import SymmetricSubgroupAsymptotics.PrimitiveAffineEightCanonicalCatalogue

/-! Composition of actual point charts into the fixed degree-eight
canonical family. No abstract group isomorphism implies a point chart. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8CanonicalPointCharts

abbrev Ambient := Equiv.Perm (Fin 8)
abbrev Has (U : Subgroup Ambient) : Prop :=
  ∃ i : Fin 24, ∃ c : Ambient, MulAut.conj c • U =
    Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.canonical i

theorem of_conjugate (U V : Subgroup Ambient) (c : Ambient)
    (hc : MulAut.conj c • U = V) (hV : Has V) : Has U := by
  obtain ⟨i, d, hd⟩ := hV
  refine ⟨i, d * c, ?_⟩
  rw [map_mul, mul_smul, hc]
  exact hd

theorem conjugated (U : Subgroup Ambient) (c : Ambient) (hU : Has U) :
    Has (MulAut.conj c • U) := by
  obtain ⟨i, d, hd⟩ := hU
  refine ⟨i, d * c⁻¹, ?_⟩
  simpa only [map_mul, mul_smul, map_inv, inv_smul_smul] using hd

end SymmetricSubgroupAsymptotics.S8CanonicalPointCharts
end
