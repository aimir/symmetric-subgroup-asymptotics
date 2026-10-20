import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow72AlgebraPolynomial
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows151To200
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250

/-! Literal inclusions transport one polynomial witness to seven joint tops. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveRow72PolynomialFamily

open DegreeTwoTwelvePairFiniteCatalogue

private theorem top_le_of_generators {m : ℕ}
    (generators : Fin m → Equiv.Perm (Fin 12)) (i j : Fin m)
    (h0 : row72Generators 0 = generators i)
    (h1 : row72Generators 1 = generators j) :
    Row72Top ≤ Subgroup.closure (Set.range generators) := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨a, rfl⟩
  fin_cases a
  · change row72Generators 0 ∈ Subgroup.closure (Set.range generators)
    rw [h0]
    exact Subgroup.subset_closure (Set.mem_range_self i)
  · change row72Generators 1 ∈ Subgroup.closure (Set.range generators)
    rw [h1]
    exact Subgroup.subset_closure (Set.mem_range_self j)

theorem top_le_row116 : Row72Top ≤ Row116Top :=
  top_le_of_generators row116Generators 0 1 (by decide +kernel) (by decide +kernel)

theorem top_le_row119 : Row72Top ≤ Row119Top :=
  top_le_of_generators row119Generators 0 2 (by decide +kernel) (by decide +kernel)

theorem top_le_row120 : Row72Top ≤ Row120Top :=
  top_le_of_generators row120Generators 0 1 (by decide +kernel) (by decide +kernel)

theorem top_le_row156 : Row72Top ≤ Row156Top :=
  top_le_of_generators row156Generators 0 2 (by decide +kernel) (by decide +kernel)

theorem top_le_row175 : Row72Top ≤ Row175Top :=
  top_le_of_generators row175Generators 0 1 (by decide +kernel) (by decide +kernel)

theorem top_le_row213 : Row72Top ≤ Row213Top :=
  top_le_of_generators row213Generators 0 2 (by decide +kernel) (by decide +kernel)

theorem row72Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row72Interface.top (Fin 12)) 1 :=
  DegreeTwoTwelveRow72AlgebraPolynomial.natural

theorem row116Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row116Interface.top (Fin 12)) 1 :=
  DegreeTwoTwelveRow72AlgebraPolynomial.natural_of_le top_le_row116

theorem row119Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row119Interface.top (Fin 12)) 1 :=
  DegreeTwoTwelveRow72AlgebraPolynomial.natural_of_le top_le_row119

theorem row120Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row120Interface.top (Fin 12)) 1 :=
  DegreeTwoTwelveRow72AlgebraPolynomial.natural_of_le top_le_row120

theorem row156Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row156Interface.top (Fin 12)) 1 :=
  DegreeTwoTwelveRow72AlgebraPolynomial.natural_of_le top_le_row156

theorem row175Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row175Interface.top (Fin 12)) 1 :=
  DegreeTwoTwelveRow72AlgebraPolynomial.natural_of_le top_le_row175

theorem row213Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row213Interface.top (Fin 12)) 1 :=
  DegreeTwoTwelveRow72AlgebraPolynomial.natural_of_le top_le_row213

end DegreeTwoTwelveRow72PolynomialFamily
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
