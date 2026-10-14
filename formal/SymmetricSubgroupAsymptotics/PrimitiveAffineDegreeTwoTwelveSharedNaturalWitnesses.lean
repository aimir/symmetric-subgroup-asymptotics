import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow1Symbolic
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows51To100
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows251To301

/-!
# Shared literal natural-module witnesses for twenty-two joint rows

Four short point-orbit tables, the natural twelve-cycle, and eight literal
inclusions of the checked row-one top supply these natural-module bounds.
They certify only the natural field of the joint-row packages; quotient
socle certificates remain independent obligations.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveSharedNaturalWitnesses

open DegreeTwoTwelvePairFiniteCatalogue

private def retarget {r : ℕ} {T S : Subgroup (Equiv.Perm (Fin 12))}
    (C : LiteralCyclicOrbitWitness T r) (g : S) (hg : g.val = C.element.val) :
    LiteralCyclicOrbitWitness S r where
  element := g
  representative := C.representative
  orbitIndex := C.orbitIndex
  exponent := C.exponent
  point_eq x := by rw [hg]; exact C.point_eq x

def row34Witness : LiteralCyclicOrbitWitness Row34Top 2 where
  element := ⟨row34Generators 0, Subgroup.subset_closure (Set.mem_range_self 0)⟩
  representative := ![0, 1]
  orbitIndex := ![0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]
  exponent := ![0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5]
  point_eq := by decide +kernel

def row58Witness : LiteralCyclicOrbitWitness Row58Top 2 :=
  retarget row34Witness
    ⟨row58Generators 2, Subgroup.subset_closure (Set.mem_range_self 2)⟩
    (by decide +kernel)

def row60Witness : LiteralCyclicOrbitWitness Row60Top 2 :=
  retarget row34Witness
    ⟨row60Generators 1, Subgroup.subset_closure (Set.mem_range_self 1)⟩
    (by decide +kernel)

def row87Witness : LiteralCyclicOrbitWitness Row87Top 2 :=
  retarget row34Witness
    ⟨row87Generators 1, Subgroup.subset_closure (Set.mem_range_self 1)⟩
    (by decide +kernel)

def row89Witness : LiteralCyclicOrbitWitness Row89Top 2 where
  element := ⟨row89Generators 1, Subgroup.subset_closure (Set.mem_range_self 1)⟩
  representative := ![0, 1]
  orbitIndex := ![0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]
  exponent := ![0, 0, 3, 1, 4, 4, 1, 5, 2, 2, 5, 3]
  point_eq := by decide +kernel

def row91Witness : LiteralCyclicOrbitWitness Row91Top 2 :=
  retarget row89Witness
    ⟨row91Generators 1, Subgroup.subset_closure (Set.mem_range_self 1)⟩
    (by decide +kernel)

def row105Witness : LiteralCyclicOrbitWitness Row105Top 1 where
  element := ⟨row105Generators 1, Subgroup.subset_closure (Set.mem_range_self 1)⟩
  representative := fun _ ↦ 0
  orbitIndex := fun _ ↦ 0
  exponent := ![0, 1, 7, 2, 8, 3, 9, 4, 10, 5, 11, 6]
  point_eq := by decide +kernel

def row108Witness : LiteralCyclicOrbitWitness Row108Top 2 :=
  retarget row34Witness
    ⟨row108Generators 2, Subgroup.subset_closure (Set.mem_range_self 2)⟩
    (by decide +kernel)

def row109Witness : LiteralCyclicOrbitWitness Row109Top 2 :=
  retarget row34Witness
    ⟨row109Generators 2, Subgroup.subset_closure (Set.mem_range_self 2)⟩
    (by decide +kernel)

def row113Witness : LiteralCyclicOrbitWitness Row113Top 2 :=
  retarget row34Witness
    ⟨row113Generators 1, Subgroup.subset_closure (Set.mem_range_self 1)⟩
    (by decide +kernel)

def row202Witness : LiteralCyclicOrbitWitness Row202Top 2 where
  element := ⟨row202Generators 2, Subgroup.subset_closure (Set.mem_range_self 2)⟩
  representative := ![0, 1]
  orbitIndex := ![0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]
  exponent := ![0, 0, 1, 1, 2, 4, 5, 3, 4, 2, 3, 5]
  point_eq := by decide +kernel

def row219Witness : LiteralCyclicOrbitWitness Row219Top 2 :=
  retarget row34Witness
    ⟨row219Generators 1, Subgroup.subset_closure (Set.mem_range_self 1)⟩
    (by decide +kernel)

def row285Witness : LiteralCyclicOrbitWitness Row285Top 2 :=
  retarget row34Witness
    ⟨row285Generators 2, Subgroup.subset_closure (Set.mem_range_self 2)⟩
    (by decide +kernel)

def row301Witness : LiteralCyclicOrbitWitness Row301Top 1 where
  element := ⟨row301Generators 0, Subgroup.subset_closure (Set.mem_range_self 0)⟩
  representative := fun _ ↦ 0
  orbitIndex := fun _ ↦ 0
  exponent := id
  point_eq := by decide +kernel

private theorem row1_le_of_generators {m : ℕ}
    (generators : Fin m → Equiv.Perm (Fin 12)) (i j : Fin m)
    (h0 : row1Generators 0 = generators i)
    (h1 : row1Generators 1 = generators j) :
    Row1Top ≤ Subgroup.closure (Set.range generators) := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨a, rfl⟩
  fin_cases a
  · change row1Generators 0 ∈ Subgroup.closure (Set.range generators)
    rw [h0]
    exact Subgroup.subset_closure (Set.mem_range_self i)
  · change row1Generators 1 ∈ Subgroup.closure (Set.range generators)
    rw [h1]
    exact Subgroup.subset_closure (Set.mem_range_self j)

theorem row1_le_row11 : Row1Top ≤ Row11Top :=
  row1_le_of_generators row11Generators 2 0 (by decide +kernel) (by decide +kernel)

theorem row1_le_row12 : Row1Top ≤ Row12Top :=
  row1_le_of_generators row12Generators 1 0 (by decide +kernel) (by decide +kernel)

theorem row1_le_row14 : Row1Top ≤ Row14Top :=
  row1_le_of_generators row14Generators 0 2 (by decide +kernel) (by decide +kernel)

theorem row1_le_row28 : Row1Top ≤ Row28Top :=
  row1_le_of_generators row28Generators 0 2 (by decide +kernel) (by decide +kernel)

theorem row1_le_row29 : Row1Top ≤ Row29Top :=
  row1_le_of_generators row29Generators 1 2 (by decide +kernel) (by decide +kernel)

theorem row1_le_row45 : Row1Top ≤ Row45Top :=
  row1_le_of_generators row45Generators 0 2 (by decide +kernel) (by decide +kernel)

theorem row1_le_row53 : Row1Top ≤ Row53Top :=
  row1_le_of_generators row53Generators 1 2 (by decide +kernel) (by decide +kernel)

theorem row1_le_row83 : Row1Top ≤ Row83Top :=
  row1_le_of_generators row83Generators 0 2 (by decide +kernel) (by decide +kernel)

theorem row11Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row11Interface.top (Fin 12)) 1 :=
  (PrimitiveAffineDegreeTwoTwelveRow1Symbolic.orbitWitness.enlargeTop row1_le_row11).uniform _

theorem row12Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row12Interface.top (Fin 12)) 1 :=
  (PrimitiveAffineDegreeTwoTwelveRow1Symbolic.orbitWitness.enlargeTop row1_le_row12).uniform _

theorem row14Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row14Interface.top (Fin 12)) 1 :=
  (PrimitiveAffineDegreeTwoTwelveRow1Symbolic.orbitWitness.enlargeTop row1_le_row14).uniform _

theorem row28Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row28Interface.top (Fin 12)) 1 :=
  (PrimitiveAffineDegreeTwoTwelveRow1Symbolic.orbitWitness.enlargeTop row1_le_row28).uniform _

theorem row29Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row29Interface.top (Fin 12)) 1 :=
  (PrimitiveAffineDegreeTwoTwelveRow1Symbolic.orbitWitness.enlargeTop row1_le_row29).uniform _

theorem row34Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row34Interface.top (Fin 12)) 2 :=
  row34Witness.uniform _

theorem row45Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row45Interface.top (Fin 12)) 1 :=
  (PrimitiveAffineDegreeTwoTwelveRow1Symbolic.orbitWitness.enlargeTop row1_le_row45).uniform _

theorem row53Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row53Interface.top (Fin 12)) 1 :=
  (PrimitiveAffineDegreeTwoTwelveRow1Symbolic.orbitWitness.enlargeTop row1_le_row53).uniform _

theorem row58Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row58Interface.top (Fin 12)) 2 :=
  row58Witness.uniform _

theorem row60Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row60Interface.top (Fin 12)) 2 :=
  row60Witness.uniform _

theorem row83Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row83Interface.top (Fin 12)) 1 :=
  (PrimitiveAffineDegreeTwoTwelveRow1Symbolic.orbitWitness.enlargeTop row1_le_row83).uniform _

theorem row87Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row87Interface.top (Fin 12)) 2 :=
  row87Witness.uniform _

theorem row89Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row89Interface.top (Fin 12)) 2 :=
  row89Witness.uniform _

theorem row91Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row91Interface.top (Fin 12)) 2 :=
  row91Witness.uniform _

theorem row105Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row105Interface.top (Fin 12)) 1 :=
  row105Witness.uniform _

theorem row108Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row108Interface.top (Fin 12)) 2 :=
  row108Witness.uniform _

theorem row109Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row109Interface.top (Fin 12)) 2 :=
  row109Witness.uniform _

theorem row113Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row113Interface.top (Fin 12)) 2 :=
  row113Witness.uniform _

theorem row202Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row202Interface.top (Fin 12)) 2 :=
  row202Witness.uniform _

theorem row219Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row219Interface.top (Fin 12)) 2 :=
  row219Witness.uniform _

theorem row285Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row285Interface.top (Fin 12)) 2 :=
  row285Witness.uniform _

theorem row301Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row301Interface.top (Fin 12)) 1 :=
  row301Witness.uniform _

end DegreeTwoTwelveSharedNaturalWitnesses
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
