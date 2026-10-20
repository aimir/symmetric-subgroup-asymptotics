import SymmetricSubgroupAsymptotics.LiteralCyclicOrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows151To200
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows251To301

/-!
# One cyclic natural-module witness for eighteen literal joint tops

The first row131 generator is a local three-cycle and the second cycles
the four triples. Their product is a twelve-cycle. Seventeen other
displayed tuples contain these same two permutations, so the one point
witness transports by literal subgroup inclusion. No top classification
or quotient-socle assertion is part of this natural-module certificate.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveRow131CyclicFamily

open DegreeTwoTwelvePairFiniteCatalogue

def first : Row131Top :=
  ⟨row131Generators 0, Subgroup.subset_closure (Set.mem_range_self 0)⟩

def second : Row131Top :=
  ⟨row131Generators 1, Subgroup.subset_closure (Set.mem_range_self 1)⟩

def witness : LiteralCyclicOrbitWitness Row131Top 1 where
  element := first * second
  representative := fun _ ↦ 0
  orbitIndex := fun _ ↦ 0
  exponent := ![0, 3, 6, 9, 4, 7, 10, 1, 8, 11, 2, 5]
  point_eq := by decide +kernel

theorem natural_of_le {T : Subgroup (Equiv.Perm (Fin 12))}
    (h : Row131Top ≤ T) : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) T (Fin 12)) 1 :=
  (witness.enlargeTop h).uniform _

private theorem top_le_of_generators {m : ℕ}
    (generators : Fin m → Equiv.Perm (Fin 12)) (i j : Fin m)
    (h0 : row131Generators 0 = generators i)
    (h1 : row131Generators 1 = generators j) :
    Row131Top ≤ Subgroup.closure (Set.range generators) := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨a, rfl⟩
  fin_cases a
  · change row131Generators 0 ∈ Subgroup.closure (Set.range generators)
    rw [h0]
    exact Subgroup.subset_closure (Set.mem_range_self i)
  · change row131Generators 1 ∈ Subgroup.closure (Set.range generators)
    rw [h1]
    exact Subgroup.subset_closure (Set.mem_range_self j)

theorem top_le_row167 : Row131Top ≤ Row167Top :=
  top_le_of_generators row167Generators 0 1 (by decide +kernel) (by decide +kernel)

theorem top_le_row169 : Row131Top ≤ Row169Top :=
  top_le_of_generators row169Generators 0 1 (by decide +kernel) (by decide +kernel)

theorem top_le_row170 : Row131Top ≤ Row170Top :=
  top_le_of_generators row170Generators 0 2 (by decide +kernel) (by decide +kernel)

theorem top_le_row209 : Row131Top ≤ Row209Top :=
  top_le_of_generators row209Generators 0 2 (by decide +kernel) (by decide +kernel)

theorem top_le_row211 : Row131Top ≤ Row211Top :=
  top_le_of_generators row211Generators 0 2 (by decide +kernel) (by decide +kernel)

theorem top_le_row217 : Row131Top ≤ Row217Top :=
  top_le_of_generators row217Generators 0 2 (by decide +kernel) (by decide +kernel)

theorem top_le_row231 : Row131Top ≤ Row231Top :=
  top_le_of_generators row231Generators 0 1 (by decide +kernel) (by decide +kernel)

theorem top_le_row245 : Row131Top ≤ Row245Top :=
  top_le_of_generators row245Generators 0 2 (by decide +kernel) (by decide +kernel)

theorem top_le_row247 : Row131Top ≤ Row247Top :=
  top_le_of_generators row247Generators 0 2 (by decide +kernel) (by decide +kernel)

theorem top_le_row248 : Row131Top ≤ Row248Top :=
  top_le_of_generators row248Generators 0 2 (by decide +kernel) (by decide +kernel)

theorem top_le_row258 : Row131Top ≤ Row258Top :=
  top_le_of_generators row258Generators 0 2 (by decide +kernel) (by decide +kernel)

theorem top_le_row263 : Row131Top ≤ Row263Top :=
  top_le_of_generators row263Generators 0 2 (by decide +kernel) (by decide +kernel)

theorem top_le_row264 : Row131Top ≤ Row264Top :=
  top_le_of_generators row264Generators 0 2 (by decide +kernel) (by decide +kernel)

theorem top_le_row267 : Row131Top ≤ Row267Top :=
  top_le_of_generators row267Generators 0 2 (by decide +kernel) (by decide +kernel)

theorem top_le_row274 : Row131Top ≤ Row274Top :=
  top_le_of_generators row274Generators 0 2 (by decide +kernel) (by decide +kernel)

theorem top_le_row281 : Row131Top ≤ Row281Top :=
  top_le_of_generators row281Generators 0 2 (by decide +kernel) (by decide +kernel)

theorem top_le_row289 : Row131Top ≤ Row289Top :=
  top_le_of_generators row289Generators 0 2 (by decide +kernel) (by decide +kernel)

theorem row131Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row131Interface.top (Fin 12)) 1 :=
  witness.uniform _

theorem row167Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row167Interface.top (Fin 12)) 1 :=
  natural_of_le top_le_row167

theorem row169Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row169Interface.top (Fin 12)) 1 :=
  natural_of_le top_le_row169

theorem row170Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row170Interface.top (Fin 12)) 1 :=
  natural_of_le top_le_row170

theorem row209Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row209Interface.top (Fin 12)) 1 :=
  natural_of_le top_le_row209

theorem row211Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row211Interface.top (Fin 12)) 1 :=
  natural_of_le top_le_row211

theorem row217Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row217Interface.top (Fin 12)) 1 :=
  natural_of_le top_le_row217

theorem row231Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row231Interface.top (Fin 12)) 1 :=
  natural_of_le top_le_row231

theorem row245Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row245Interface.top (Fin 12)) 1 :=
  natural_of_le top_le_row245

theorem row247Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row247Interface.top (Fin 12)) 1 :=
  natural_of_le top_le_row247

theorem row248Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row248Interface.top (Fin 12)) 1 :=
  natural_of_le top_le_row248

theorem row258Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row258Interface.top (Fin 12)) 1 :=
  natural_of_le top_le_row258

theorem row263Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row263Interface.top (Fin 12)) 1 :=
  natural_of_le top_le_row263

theorem row264Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row264Interface.top (Fin 12)) 1 :=
  natural_of_le top_le_row264

theorem row267Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row267Interface.top (Fin 12)) 1 :=
  natural_of_le top_le_row267

theorem row274Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row274Interface.top (Fin 12)) 1 :=
  natural_of_le top_le_row274

theorem row281Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row281Interface.top (Fin 12)) 1 :=
  natural_of_le top_le_row281

theorem row289Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row289Interface.top (Fin 12)) 1 :=
  natural_of_le top_le_row289

end DegreeTwoTwelveRow131CyclicFamily
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
