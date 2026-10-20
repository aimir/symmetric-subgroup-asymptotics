import SymmetricSubgroupAsymptotics.TernarySignedBlockCoordinates
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFourTernaryFiniteWitnessData

/-!
# The eight literal four-ternary coordinate tuples

A phase change inside each original three-point block removes every affine
offset from the nontranslation generators. The coordinate closure is then
identified faithfully with the original top, retaining every point label.
The padded fifth generator is the identity in the seven four-generator rows.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoFourTernaryCoordinates

open TernarySignedBlockCoordinates
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def padOne {G : Type} [One G] (g : Fin 4 → G) : Fin 5 → G :=
  ![g 0, g 1, g 2, g 3, 1]

theorem padOne_closure {G : Type} [Group G] (g : Fin 4 → G) :
    Subgroup.closure (Set.range (padOne g)) = Subgroup.closure (Set.range g) := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact Subgroup.subset_closure (Set.mem_range_self (0 : Fin 4))
    · exact Subgroup.subset_closure (Set.mem_range_self (1 : Fin 4))
    · exact Subgroup.subset_closure (Set.mem_range_self (2 : Fin 4))
    · exact Subgroup.subset_closure (Set.mem_range_self (3 : Fin 4))
    · exact Subgroup.one_mem _
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact Subgroup.subset_closure (Set.mem_range_self (f := padOne g) (0 : Fin 5))
    · exact Subgroup.subset_closure (Set.mem_range_self (f := padOne g) (1 : Fin 5))
    · exact Subgroup.subset_closure (Set.mem_range_self (f := padOne g) (2 : Fin 5))
    · exact Subgroup.subset_closure (Set.mem_range_self (f := padOne g) (3 : Fin 5))

def literalGenerators : Fin 8 → Fin 5 → Equiv.Perm (Fin 12) :=
  ![padOne row37Generators, padOne row77Generators, padOne row117Generators,
    padOne row168Generators, padOne row210Generators, padOne row214Generators,
    row242Generators, padOne row261Generators]

theorem literal_closure_eq (r : Fin 8) :
    Subgroup.closure (Set.range (literalGenerators r)) =
      (degreeTwoFourTernaryInterface r).top := by
  fin_cases r
  · exact padOne_closure row37Generators
  · exact padOne_closure row77Generators
  · exact padOne_closure row117Generators
  · exact padOne_closure row168Generators
  · exact padOne_closure row210Generators
  · exact padOne_closure row214Generators
  · rfl
  · exact padOne_closure row261Generators

theorem literalGenerator_mem (r : Fin 8) (j : Fin 5) :
    literalGenerators r j ∈ (degreeTwoFourTernaryInterface r).top := by
  rw [← literal_closure_eq]
  exact Subgroup.subset_closure (Set.mem_range_self j)

def phase : Fin 8 → Vector :=
  ![![1, 2, 0, 1], ![1, 2, 0, 1], ![1, 2, 0, 1], ![1, 2, 0, 1],
    ![1, 2, 0, 1], ![0, 2, 2, 1], ![1, 2, 0, 1], ![1, 2, 0, 1]]

def blockOne : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3
def blockTwo : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3
def blockThree : Equiv.Perm (Fin 4) := Equiv.swap 0 3 * Equiv.swap 1 2

def allMinus : Signed := ⟨![-1, -1, -1, -1], 1⟩
def oddMinus : Signed := ⟨![1, -1, 1, -1], 1⟩
def highMinus : Signed := ⟨![1, 1, -1, -1], 1⟩
def lastMinus : Signed := ⟨![1, 1, 1, -1], 1⟩
def moveOne : Signed := ⟨1, blockOne⟩
def moveTwo : Signed := ⟨1, blockTwo⟩
def twistedTwo : Signed := ⟨![1, -1, -1, 1], blockTwo⟩
def moveThree : Signed := ⟨1, blockThree⟩

def pairedSeed : Vector := ![0, 1, 0, 1]
def augmentationSeed : Vector := ![0, 1, 1, 1]
def lastSeed : Vector := ![0, 0, 0, 1]

/-- One pure translation followed by the exact signed Klein-block motions. -/
def generators : Fin 8 → Fin 5 → Affine :=
  ![
    ![translate pairedSeed, signed allMinus, signed moveOne, signed moveTwo, 1],
    ![translate pairedSeed, signed oddMinus, signed moveOne, signed moveTwo, 1],
    ![translate augmentationSeed, signed allMinus, signed moveOne, signed moveTwo, 1],
    ![translate lastSeed, signed allMinus, signed moveOne, signed moveTwo, 1],
    ![translate lastSeed, signed oddMinus, signed moveOne, signed moveTwo, 1],
    ![translate lastSeed, signed oddMinus, signed twistedTwo, signed moveThree, 1],
    ![translate lastSeed, signed highMinus, signed oddMinus, signed moveOne, signed moveTwo],
    ![translate lastSeed, signed lastMinus, signed moveOne, signed moveTwo, 1]
    ]

/-- Only the forty displayed generators on twelve points are checked. -/
theorem generators_binding (r : Fin 8) (j : Fin 5) :
    literalAction (phase r) (generators r j) = literalGenerators r j := by
  fin_cases r <;> fin_cases j <;>
    apply Equiv.ext <;> intro x <;> revert x <;> decide +kernel

abbrev CoordinateTop (r : Fin 8) : Subgroup Affine :=
  Subgroup.closure (Set.range (generators r))

/-- No group-cardinality premise enters the exact original-top binding. -/
noncomputable def originalEquiv (r : Fin 8) :
    CoordinateTop r ≃* (degreeTwoFourTernaryInterface r).top :=
  (closureEquiv (phase r) (generators r) (literalGenerators r)
    (generators_binding r)).trans (MulEquiv.subgroupCongr (literal_closure_eq r))

theorem chart_block (r : Fin 8) (x : Fin 12) :
    (pointChart (phase r) x).2 = degreeTwoFourTernaryBlock x := by
  change (baseChart x).2 = degreeTwoFourTernaryBlock x
  revert x
  decide +kernel

end PrimitiveAffineDegreeTwoFourTernaryCoordinates
end SymmetricSubgroupAsymptotics

end
