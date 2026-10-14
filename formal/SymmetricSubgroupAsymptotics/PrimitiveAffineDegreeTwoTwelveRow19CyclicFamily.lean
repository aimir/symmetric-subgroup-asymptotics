import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow19FinitePackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows51To100
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150

/-!
# Six further natural-module bounds from the literal row-19 cycle

Each displayed target tuple contains the two original row-19 generators.
The same twelve-cycle therefore proves the natural-module bound one on
these exact tops. The inclusions make no assertion about quotient socles.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveRow19CyclicFamily

open DegreeTwoTwelvePairFiniteCatalogue

theorem natural_of_le {T : Subgroup (Equiv.Perm (Fin 12))}
    (h : Row19Top ≤ T) : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) T (Fin 12)) 1 :=
  (DegreeTwoTwelveRow19FinitePackage.witness.enlargeTop h).uniform _

private theorem top_le_of_generators {m : ℕ}
    (generators : Fin m → Equiv.Perm (Fin 12)) (i j : Fin m)
    (h0 : row19Generators 0 = generators i)
    (h1 : row19Generators 1 = generators j) :
    Row19Top ≤ Subgroup.closure (Set.range generators) := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨a, rfl⟩
  fin_cases a
  · change row19Generators 0 ∈ Subgroup.closure (Set.range generators)
    rw [h0]
    exact Subgroup.subset_closure (Set.mem_range_self i)
  · change row19Generators 1 ∈ Subgroup.closure (Set.range generators)
    rw [h1]
    exact Subgroup.subset_closure (Set.mem_range_self j)

theorem top_le_row38 : Row19Top ≤ Row38Top :=
  top_le_of_generators row38Generators 0 1 (by decide +kernel) (by decide +kernel)

theorem top_le_row39 : Row19Top ≤ Row39Top :=
  top_le_of_generators row39Generators 0 2 (by decide +kernel) (by decide +kernel)

theorem top_le_row42 : Row19Top ≤ Row42Top :=
  top_le_of_generators row42Generators 0 1 (by decide +kernel) (by decide +kernel)

theorem top_le_row79 : Row19Top ≤ Row79Top :=
  top_le_of_generators row79Generators 0 2 (by decide +kernel) (by decide +kernel)

theorem top_le_row81 : Row19Top ≤ Row81Top :=
  top_le_of_generators row81Generators 0 2 (by decide +kernel) (by decide +kernel)

theorem top_le_row125 : Row19Top ≤ Row125Top :=
  top_le_of_generators row125Generators 0 2 (by decide +kernel) (by decide +kernel)

theorem row38Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row38Interface.top (Fin 12)) 1 :=
  natural_of_le top_le_row38

theorem row39Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row39Interface.top (Fin 12)) 1 :=
  natural_of_le top_le_row39

theorem row42Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row42Interface.top (Fin 12)) 1 :=
  natural_of_le top_le_row42

theorem row79Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row79Interface.top (Fin 12)) 1 :=
  natural_of_le top_le_row79

theorem row81Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row81Interface.top (Fin 12)) 1 :=
  natural_of_le top_le_row81

theorem row125Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row125Interface.top (Fin 12)) 1 :=
  natural_of_le top_le_row125

end DegreeTwoTwelveRow19CyclicFamily
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
