import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSignedSubgroupSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows151To200

/-! Fourteen original signed affine actions at explicit alternate
capacities. The common theorem retains both actual elementary kernels;
only their C4 or D8 block projection is identified with a standard model. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSignedAlternateSocles

open FourBlockBinarySignSpaces FourBlockSignedSubgroupLiteralSocles
open PrimitiveAffineDegreeTwoTwelveSignedSubgroupSocles
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def middleRelabel : Equiv.Perm (Fin 4) := Equiv.swap 1 2

def row46Lifts : Fin 3 → Model (R := Cyclic) :=
  ![lift ![1,1,1,0] 0 1,
    lift 0 ![1,1,1,1] 1,
    lift 0 ![0,1,0,0] cyclicGenerator]
def row173Lifts : Fin 3 → Model (R := Cyclic) :=
  ![lift ![1,0,0,0] 0 1,
    lift 0 ![1,1,1,1] 1,
    lift 0 ![0,0,0,1] cyclicGenerator]

def row35Lifts : Fin 3 → Model (R := Dihedral) :=
  ![lift ![1,0,1,0] 0 1,
    lift ![1,0,1,0] ![1,0,1,0] (dihedralReflection*dihedralRotation^2),
    lift ![2,1,2,1] 0 (dihedralReflection*dihedralRotation)]
def row36Lifts : Fin 2 → Model (R := Dihedral) :=
  ![lift ![2,2,2,2] 0 (dihedralReflection*dihedralRotation),
    lift ![2,1,1,2] ![1,0,1,0] dihedralReflection]
def row80Lifts : Fin 4 → Model (R := Dihedral) :=
  ![lift ![2,1,1,2] 0 (dihedralRotation^2),
    lift ![0,1,0,1] 0 1,
    lift ![2,2,1,2] ![1,0,1,0] (dihedralReflection*dihedralRotation),
    lift ![0,2,0,2] ![0,1,0,1] dihedralReflection]
def row82Lifts : Fin 4 → Model (R := Dihedral) :=
  ![lift ![2,0,1,0] 0 (dihedralReflection*dihedralRotation^2),
    lift ![1,0,1,0] 0 1,
    lift ![0,2,2,0] ![1,1,1,1] 1,
    lift ![0,2,0,0] ![0,1,0,1] (dihedralReflection*dihedralRotation)]
def row84Lifts : Fin 4 → Model (R := Dihedral) :=
  ![lift ![1,1,1,0] 0 1,
    lift 0 ![1,1,1,1] 1,
    lift 0 ![0,1,0,0] dihedralRotation,
    lift ![1,1,1,0] ![1,1,1,0] (dihedralReflection*dihedralRotation^2)]
def row209Lifts : Fin 4 → Model (R := Dihedral) :=
  ![lift ![1,0,0,0] 0 1,
    lift 0 ![1,1,1,1] 1,
    lift 0 0 dihedralRotation,
    lift 0 ![1,0,1,0] dihedralReflection]
def row212Lifts : Fin 4 → Model (R := Dihedral) :=
  ![lift ![1,0,0,0] 0 1,
    lift 0 ![1,1,1,1] 1,
    lift 0 ![1,0,0,1] (dihedralReflection*dihedralRotation^3),
    lift ![0,2,2,2] ![0,1,1,1] dihedralReflection]
def row216Lifts : Fin 4 → Model (R := Dihedral) :=
  ![lift ![1,0,0,0] 0 1,
    lift 0 ![1,1,1,1] 1,
    lift 0 0 (dihedralReflection*dihedralRotation),
    lift ![0,2,2,2] ![0,1,1,1] dihedralReflection]
def row247Lifts : Fin 4 → Model (R := Dihedral) :=
  ![lift ![1,0,0,0] 0 1,
    lift 0 ![1,0,1,0] 1,
    lift 0 0 dihedralRotation,
    lift 0 ![0,0,1,1] (dihedralReflection*dihedralRotation^3)]
def row249Lifts : Fin 4 → Model (R := Dihedral) :=
  ![lift ![1,0,0,0] 0 1,
    lift 0 ![1,0,1,0] 1,
    lift 0 ![0,0,1,0] (dihedralReflection*dihedralRotation^2),
    lift ![2,1,2,1] 0 (dihedralReflection*dihedralRotation)]
def row262Lifts : Fin 5 → Model (R := Dihedral) :=
  ![lift ![1,0,0,0] 0 1,
    lift 0 ![1,0,1,0] 1,
    lift 0 0 (dihedralReflection*dihedralRotation^2),
    lift 0 0 dihedralReflection,
    lift 0 ![0,1,1,1] dihedralRotation]
def row263Lifts : Fin 4 → Model (R := Dihedral) :=
  ![lift ![1,0,0,0] 0 1,
    lift 0 ![1,0,1,0] 1,
    lift 0 0 dihedralRotation,
    lift 0 ![1,0,1,1] dihedralReflection]

theorem row46_bindings (i : Fin 3) : action middleRelabel (row46Lifts i) = row46Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel
theorem row173_bindings (i : Fin 3) : action 1 (row173Lifts i) = row173Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel
theorem row35_bindings (i : Fin 3) : action 1 (row35Lifts i) = row35Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel
theorem row36_bindings (i : Fin 2) : action relabel (row36Lifts i) = row36Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel
theorem row80_bindings (i : Fin 4) : action relabel (row80Lifts i) = row80Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel
theorem row82_bindings (i : Fin 4) : action relabel (row82Lifts i) = row82Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel
theorem row84_bindings (i : Fin 4) : action middleRelabel (row84Lifts i) = row84Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel
theorem row209_bindings (i : Fin 4) : action 1 (row209Lifts i) = row209Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel
theorem row212_bindings (i : Fin 4) : action relabel (row212Lifts i) = row212Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel
theorem row216_bindings (i : Fin 4) : action relabel (row216Lifts i) = row216Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel
theorem row247_bindings (i : Fin 4) : action 1 (row247Lifts i) = row247Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel
theorem row249_bindings (i : Fin 4) : action 1 (row249Lifts i) = row249Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel
theorem row262_bindings (i : Fin 5) : action 1 (row262Lifts i) = row262Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel
theorem row263_bindings (i : Fin 4) : action 1 (row263Lifts i) = row263Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

theorem dihedral_full_from_rotation {n : ℕ} (lifted : Fin n → Model (R := Dihedral))
    (i : Fin n) (k : ℕ)
    (hc : dihedralRotation ∈ Subgroup.closure (Set.range (fun j => (lifted j).right.right)))
    (hi : (lifted i).right.right = dihedralReflection*dihedralRotation^k) :
    Subgroup.closure (Set.range (fun j => (lifted j).right.right)) = ⊤ := by
  let B := Subgroup.closure (Set.range (fun j => (lifted j).right.right))
  have hmem : (lifted i).right.right ∈ B := Subgroup.subset_closure (Set.mem_range_self i)
  have hr : dihedralReflection ∈ B := by
    have h := B.mul_mem hmem (B.inv_mem (B.pow_mem hc k))
    rw [hi,mul_inv_cancel_right] at h
    exact h
  exact top_unique (fun r _ => dihedral_mem B hc hr r)

theorem row35_blocks :
    Subgroup.closure (Set.range (fun i => (row35Lifts i).right.right)) = ⊤ := by
  apply dihedral_full_from_rotation row35Lifts 1 2 ?_ rfl
  have he : (row35Lifts 2).right.right * (row35Lifts 1).right.right = dihedralRotation := by
    apply Subtype.ext; decide +kernel
  rw [← he]
  exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_range_self 2))
    (Subgroup.subset_closure (Set.mem_range_self 1))
theorem row36_blocks :
    Subgroup.closure (Set.range (fun i => (row36Lifts i).right.right)) = ⊤ := by
  apply dihedral_full row36Lifts 1 0 rfl
  right; apply Subtype.ext; decide +kernel
theorem row80_blocks :
    Subgroup.closure (Set.range (fun i => (row80Lifts i).right.right)) = ⊤ := by
  apply dihedral_full row80Lifts 3 2 rfl
  right; apply Subtype.ext; decide +kernel
theorem row82_blocks :
    Subgroup.closure (Set.range (fun i => (row82Lifts i).right.right)) = ⊤ := by
  apply dihedral_full_from_rotation row82Lifts 0 2 ?_ rfl
  have he : (row82Lifts 3).right.right * (row82Lifts 0).right.right = dihedralRotation := by
    apply Subtype.ext; decide +kernel
  rw [← he]
  exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_range_self 3))
    (Subgroup.subset_closure (Set.mem_range_self 0))
theorem row84_blocks :
    Subgroup.closure (Set.range (fun i => (row84Lifts i).right.right)) = ⊤ := by
  apply dihedral_full_from_rotation row84Lifts 3 2 ?_ rfl
  exact Subgroup.subset_closure (Set.mem_range_self (2 : Fin 4))
theorem row209_blocks :
    Subgroup.closure (Set.range (fun i => (row209Lifts i).right.right)) = ⊤ := by
  apply dihedral_full_from_rotation row209Lifts 3 0 ?_ ?_
  · exact Subgroup.subset_closure (Set.mem_range_self (2 : Fin 4))
  · simp only [pow_zero,mul_one]; rfl
theorem row212_blocks :
    Subgroup.closure (Set.range (fun i => (row212Lifts i).right.right)) = ⊤ := by
  apply dihedral_full row212Lifts 3 2 rfl
  left; apply Subtype.ext; decide +kernel
theorem row216_blocks :
    Subgroup.closure (Set.range (fun i => (row216Lifts i).right.right)) = ⊤ := by
  apply dihedral_full row216Lifts 3 2 rfl
  right; apply Subtype.ext; decide +kernel
theorem row247_blocks :
    Subgroup.closure (Set.range (fun i => (row247Lifts i).right.right)) = ⊤ := by
  apply dihedral_full_from_rotation row247Lifts 3 3 ?_ rfl
  exact Subgroup.subset_closure (Set.mem_range_self (2 : Fin 4))
theorem row249_blocks :
    Subgroup.closure (Set.range (fun i => (row249Lifts i).right.right)) = ⊤ := by
  apply dihedral_full_from_rotation row249Lifts 2 2 ?_ rfl
  have he : (row249Lifts 3).right.right * (row249Lifts 2).right.right = dihedralRotation := by
    apply Subtype.ext; decide +kernel
  rw [← he]
  exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_range_self 3))
    (Subgroup.subset_closure (Set.mem_range_self 2))
theorem row262_blocks :
    Subgroup.closure (Set.range (fun i => (row262Lifts i).right.right)) = ⊤ := by
  apply dihedral_full_from_rotation row262Lifts 3 0 ?_ ?_
  · exact Subgroup.subset_closure (Set.mem_range_self (4 : Fin 5))
  · simp only [pow_zero,mul_one]; rfl
theorem row263_blocks :
    Subgroup.closure (Set.range (fun i => (row263Lifts i).right.right)) = ⊤ := by
  apply dihedral_full_from_rotation row263Lifts 3 0 ?_ ?_
  · exact Subgroup.subset_closure (Set.mem_range_self (2 : Fin 4))
  · simp only [pow_zero,mul_one]; rfl

theorem row46AtTwo_quotientSocle (N : Subgroup Row46Top) [N.Normal] :
    SocleNormalGeneratorBound (Row46Top ⧸ N) 2 :=
  quotientSocle middleRelabel row46Lifts row46Generators row46_bindings
    (cyclic_full row46Lifts 2 rfl) cyclic_transitive cyclic_coprime 1 1
    cyclic_uniform cyclic_normalGen N
theorem row173AtTwo_quotientSocle (N : Subgroup Row173Top) [N.Normal] :
    SocleNormalGeneratorBound (Row173Top ⧸ N) 2 :=
  quotientSocle 1 row173Lifts row173Generators row173_bindings
    (cyclic_full row173Lifts 2 rfl) cyclic_transitive cyclic_coprime 1 1
    cyclic_uniform cyclic_normalGen N
theorem row35AtThree_quotientSocle (N : Subgroup Row35Top) [N.Normal] :
    SocleNormalGeneratorBound (Row35Top ⧸ N) 3 :=
  quotientSocle 1 row35Lifts row35Generators row35_bindings
    row35_blocks dihedral_transitive dihedral_coprime 1 2 dihedral_uniform dihedral_normalGen N
theorem row36AtThree_quotientSocle (N : Subgroup Row36Top) [N.Normal] :
    SocleNormalGeneratorBound (Row36Top ⧸ N) 3 :=
  quotientSocle relabel row36Lifts row36Generators row36_bindings
    row36_blocks dihedral_transitive dihedral_coprime 1 2 dihedral_uniform dihedral_normalGen N
theorem row80AtThree_quotientSocle (N : Subgroup Row80Top) [N.Normal] :
    SocleNormalGeneratorBound (Row80Top ⧸ N) 3 :=
  quotientSocle relabel row80Lifts row80Generators row80_bindings
    row80_blocks dihedral_transitive dihedral_coprime 1 2 dihedral_uniform dihedral_normalGen N
theorem row82AtThree_quotientSocle (N : Subgroup Row82Top) [N.Normal] :
    SocleNormalGeneratorBound (Row82Top ⧸ N) 3 :=
  quotientSocle relabel row82Lifts row82Generators row82_bindings
    row82_blocks dihedral_transitive dihedral_coprime 1 2 dihedral_uniform dihedral_normalGen N
theorem row84AtThree_quotientSocle (N : Subgroup Row84Top) [N.Normal] :
    SocleNormalGeneratorBound (Row84Top ⧸ N) 3 :=
  quotientSocle middleRelabel row84Lifts row84Generators row84_bindings
    row84_blocks dihedral_transitive dihedral_coprime 1 2 dihedral_uniform dihedral_normalGen N
theorem row209AtThree_quotientSocle (N : Subgroup Row209Top) [N.Normal] :
    SocleNormalGeneratorBound (Row209Top ⧸ N) 3 :=
  quotientSocle 1 row209Lifts row209Generators row209_bindings
    row209_blocks dihedral_transitive dihedral_coprime 1 2 dihedral_uniform dihedral_normalGen N
theorem row212AtThree_quotientSocle (N : Subgroup Row212Top) [N.Normal] :
    SocleNormalGeneratorBound (Row212Top ⧸ N) 3 :=
  quotientSocle relabel row212Lifts row212Generators row212_bindings
    row212_blocks dihedral_transitive dihedral_coprime 1 2 dihedral_uniform dihedral_normalGen N
theorem row216AtThree_quotientSocle (N : Subgroup Row216Top) [N.Normal] :
    SocleNormalGeneratorBound (Row216Top ⧸ N) 3 :=
  quotientSocle relabel row216Lifts row216Generators row216_bindings
    row216_blocks dihedral_transitive dihedral_coprime 1 2 dihedral_uniform dihedral_normalGen N
theorem row247AtThree_quotientSocle (N : Subgroup Row247Top) [N.Normal] :
    SocleNormalGeneratorBound (Row247Top ⧸ N) 3 :=
  quotientSocle 1 row247Lifts row247Generators row247_bindings
    row247_blocks dihedral_transitive dihedral_coprime 1 2 dihedral_uniform dihedral_normalGen N
theorem row249AtThree_quotientSocle (N : Subgroup Row249Top) [N.Normal] :
    SocleNormalGeneratorBound (Row249Top ⧸ N) 3 :=
  quotientSocle 1 row249Lifts row249Generators row249_bindings
    row249_blocks dihedral_transitive dihedral_coprime 1 2 dihedral_uniform dihedral_normalGen N
theorem row262AtThree_quotientSocle (N : Subgroup Row262Top) [N.Normal] :
    SocleNormalGeneratorBound (Row262Top ⧸ N) 3 :=
  quotientSocle 1 row262Lifts row262Generators row262_bindings
    row262_blocks dihedral_transitive dihedral_coprime 1 2 dihedral_uniform dihedral_normalGen N
theorem row263AtThree_quotientSocle (N : Subgroup Row263Top) [N.Normal] :
    SocleNormalGeneratorBound (Row263Top ⧸ N) 3 :=
  quotientSocle 1 row263Lifts row263Generators row263_bindings
    row263_blocks dihedral_transitive dihedral_coprime 1 2 dihedral_uniform dihedral_normalGen N

def row46AtTwo_family : row46Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row46Interface.normalRegistry (fun N => by letI := N.2; exact row46AtTwo_quotientSocle N.1)
def row173AtTwo_family : row173Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row173Interface.normalRegistry (fun N => by letI := N.2; exact row173AtTwo_quotientSocle N.1)
def row35AtThree_family : row35Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row35Interface.normalRegistry (fun N => by letI := N.2; exact row35AtThree_quotientSocle N.1)
def row36AtThree_family : row36Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row36Interface.normalRegistry (fun N => by letI := N.2; exact row36AtThree_quotientSocle N.1)
def row80AtThree_family : row80Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row80Interface.normalRegistry (fun N => by letI := N.2; exact row80AtThree_quotientSocle N.1)
def row82AtThree_family : row82Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row82Interface.normalRegistry (fun N => by letI := N.2; exact row82AtThree_quotientSocle N.1)
def row84AtThree_family : row84Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row84Interface.normalRegistry (fun N => by letI := N.2; exact row84AtThree_quotientSocle N.1)
def row209AtThree_family : row209Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row209Interface.normalRegistry (fun N => by letI := N.2; exact row209AtThree_quotientSocle N.1)
def row212AtThree_family : row212Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row212Interface.normalRegistry (fun N => by letI := N.2; exact row212AtThree_quotientSocle N.1)
def row216AtThree_family : row216Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row216Interface.normalRegistry (fun N => by letI := N.2; exact row216AtThree_quotientSocle N.1)
def row247AtThree_family : row247Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row247Interface.normalRegistry (fun N => by letI := N.2; exact row247AtThree_quotientSocle N.1)
def row249AtThree_family : row249Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row249Interface.normalRegistry (fun N => by letI := N.2; exact row249AtThree_quotientSocle N.1)
def row262AtThree_family : row262Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row262Interface.normalRegistry (fun N => by letI := N.2; exact row262AtThree_quotientSocle N.1)
def row263AtThree_family : row263Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row263Interface.normalRegistry (fun N => by letI := N.2; exact row263AtThree_quotientSocle N.1)

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSignedAlternateSocles

end
