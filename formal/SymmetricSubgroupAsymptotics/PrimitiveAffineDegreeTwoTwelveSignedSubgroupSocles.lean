import SymmetricSubgroupAsymptotics.FourBlockSignedSubgroupLiteralSocles
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows1To50
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows51To100
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows251To301

/-! Six original joint rows with retained signed affine lifts. The block
projection is generated symbolically; the full affine subgroup is never
identified with a split model. Both elementary kernels and every original
normal quotient are retained by the common subgroup theorem. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSignedSubgroupSocles

open FourBlockBinarySignSpaces FourBlockSignedSubgroupLiteralSocles
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def relabel : Equiv.Perm (Fin 4) := Equiv.swap 2 3

def row41Lifts : Fin 4 → Model (R := Cyclic) :=
  ![lift ![2,1,1,2] 0 (cyclicGenerator^2),
    lift ![1,0,1,0] 0 1,
    lift ![0,2,2,0] ![1,1,1,1] 1,
    lift ![0,1,0,1] ![0,1,0,1] cyclicGenerator]

def row215Lifts : Fin 4 → Model (R := Cyclic) :=
  ![lift ![1,0,0,0] 0 1,
    lift 0 ![1,0,1,0] 1,
    lift ![0,2,0,0] ![0,1,1,0] (cyclicGenerator^2),
    lift ![2,1,2,1] ![0,1,0,0] cyclicGenerator]

def row244Lifts : Fin 4 → Model (R := Cyclic) :=
  ![lift ![1,0,0,0] 0 1,
    lift 0 ![1,0,1,0] 1,
    lift 0 0 (cyclicGenerator^2),
    lift 0 ![0,1,1,1] cyclicGenerator]

def row78Lifts : Fin 4 → Model (R := Dihedral) :=
  ![lift ![2,1,1,2] 0 (dihedralRotation^2),
    lift ![2,2,2,2] 0 (dihedralReflection*dihedralRotation),
    lift ![0,1,2,2] ![1,1,1,1] (dihedralReflection*dihedralRotation),
    lift ![0,2,0,2] ![0,1,0,1] dihedralReflection]

def row243Lifts : Fin 4 → Model (R := Dihedral) :=
  ![lift ![1,0,0,0] 0 1,
    lift 0 ![1,0,1,0] 1,
    lift 0 0 (dihedralReflection*dihedralRotation^3),
    lift ![0,0,1,0] ![0,0,1,0] dihedralReflection]

def row266Lifts : Fin 5 → Model (R := Dihedral) :=
  ![lift ![1,0,0,0] 0 1,
    lift 0 ![1,0,1,0] 1,
    lift 0 0 (dihedralReflection*dihedralRotation^3),
    lift 0 0 (dihedralRotation^2),
    lift 0 ![1,0,1,1] dihedralReflection]

theorem row41_bindings (i : Fin 4) : action relabel (row41Lifts i) = row41Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel
theorem row215_bindings (i : Fin 4) : action 1 (row215Lifts i) = row215Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel
theorem row244_bindings (i : Fin 4) : action 1 (row244Lifts i) = row244Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel
theorem row78_bindings (i : Fin 4) : action relabel (row78Lifts i) = row78Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel
theorem row243_bindings (i : Fin 4) : action 1 (row243Lifts i) = row243Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel
theorem row266_bindings (i : Fin 5) : action 1 (row266Lifts i) = row266Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

theorem cyclic_full {n : ℕ} (lifted : Fin n → Model (R := Cyclic))
    (i : Fin n) (hi : (lifted i).right.right = cyclicGenerator) :
    Subgroup.closure (Set.range (fun j => (lifted j).right.right)) = ⊤ := by
  apply top_unique
  intro r _
  apply cyclic_mem _ ?_ r
  rw [← hi]
  exact Subgroup.subset_closure (Set.mem_range_self i)

theorem dihedral_full {n : ℕ} (lifted : Fin n → Model (R := Dihedral))
    (i j : Fin n) (hi : (lifted i).right.right = dihedralReflection)
    (hc : (lifted j).right.right * (lifted i).right.right = dihedralRotation ∨
      (lifted i).right.right * (lifted j).right.right = dihedralRotation) :
    Subgroup.closure (Set.range (fun k => (lifted k).right.right)) = ⊤ := by
  let B := Subgroup.closure (Set.range (fun k => (lifted k).right.right))
  have hmem (k : Fin n) : (lifted k).right.right ∈ B :=
    Subgroup.subset_closure (Set.mem_range_self k)
  have hr : dihedralReflection ∈ B := hi ▸ hmem i
  have hrot : dihedralRotation ∈ B := by
    rcases hc with hc | hc
    · exact hc ▸ B.mul_mem (hmem j) (hmem i)
    · exact hc ▸ B.mul_mem (hmem i) (hmem j)
  exact top_unique (fun r _ => dihedral_mem B hrot hr r)

theorem row78_blocks :
    Subgroup.closure (Set.range (fun i => (row78Lifts i).right.right)) = ⊤ := by
  apply dihedral_full row78Lifts 3 1 rfl
  right
  apply Subtype.ext
  decide +kernel

theorem row243_blocks :
    Subgroup.closure (Set.range (fun i => (row243Lifts i).right.right)) = ⊤ := by
  apply dihedral_full row243Lifts 3 2 rfl
  left
  apply Subtype.ext
  decide +kernel

theorem row266_blocks :
    Subgroup.closure (Set.range (fun i => (row266Lifts i).right.right)) = ⊤ := by
  apply dihedral_full row266Lifts 4 2 rfl
  left
  apply Subtype.ext
  decide +kernel

theorem cyclic_transitive (i : Fin 4) : ∃ r : Cyclic, r • 0 = i := by
  obtain ⟨n,hn⟩ := cyclic_orbit i
  exact ⟨cyclicGenerator^n,hn⟩

theorem dihedral_transitive (i : Fin 4) : ∃ r : Dihedral, r • 0 = i := by
  obtain ⟨n,hn⟩ := dihedral_orbit i
  exact ⟨dihedralRotation^n,hn⟩

theorem row41_quotientSocle (N : Subgroup Row41Top) [N.Normal] :
    SocleNormalGeneratorBound (Row41Top ⧸ N) 2 :=
  quotientSocle relabel row41Lifts row41Generators row41_bindings
    (cyclic_full row41Lifts 3 rfl) cyclic_transitive cyclic_coprime 1 1
    cyclic_uniform cyclic_normalGen N

theorem row215_quotientSocle (N : Subgroup Row215Top) [N.Normal] :
    SocleNormalGeneratorBound (Row215Top ⧸ N) 2 :=
  quotientSocle 1 row215Lifts row215Generators row215_bindings
    (cyclic_full row215Lifts 3 rfl) cyclic_transitive cyclic_coprime 1 1
    cyclic_uniform cyclic_normalGen N

theorem row244_quotientSocle (N : Subgroup Row244Top) [N.Normal] :
    SocleNormalGeneratorBound (Row244Top ⧸ N) 2 :=
  quotientSocle 1 row244Lifts row244Generators row244_bindings
    (cyclic_full row244Lifts 3 rfl) cyclic_transitive cyclic_coprime 1 1
    cyclic_uniform cyclic_normalGen N

theorem row78_quotientSocle (N : Subgroup Row78Top) [N.Normal] :
    SocleNormalGeneratorBound (Row78Top ⧸ N) 3 :=
  quotientSocle relabel row78Lifts row78Generators row78_bindings
    row78_blocks dihedral_transitive dihedral_coprime 1 2
    dihedral_uniform dihedral_normalGen N

theorem row243_quotientSocle (N : Subgroup Row243Top) [N.Normal] :
    SocleNormalGeneratorBound (Row243Top ⧸ N) 3 :=
  quotientSocle 1 row243Lifts row243Generators row243_bindings
    row243_blocks dihedral_transitive dihedral_coprime 1 2
    dihedral_uniform dihedral_normalGen N

theorem row266_quotientSocle (N : Subgroup Row266Top) [N.Normal] :
    SocleNormalGeneratorBound (Row266Top ⧸ N) 3 :=
  quotientSocle 1 row266Lifts row266Generators row266_bindings
    row266_blocks dihedral_transitive dihedral_coprime 1 2
    dihedral_uniform dihedral_normalGen N

def row41_family : row41Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row41Interface.normalRegistry (fun N => by letI := N.2; exact row41_quotientSocle N.1)
def row78_family : row78Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row78Interface.normalRegistry (fun N => by letI := N.2; exact row78_quotientSocle N.1)
def row215_family : row215Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row215Interface.normalRegistry (fun N => by letI := N.2; exact row215_quotientSocle N.1)
def row243_family : row243Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row243Interface.normalRegistry (fun N => by letI := N.2; exact row243_quotientSocle N.1)
def row244_family : row244Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row244Interface.normalRegistry (fun N => by letI := N.2; exact row244_quotientSocle N.1)
def row266_family : row266Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row266Interface.normalRegistry (fun N => by letI := N.2; exact row266_quotientSocle N.1)

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSignedSubgroupSocles

end
