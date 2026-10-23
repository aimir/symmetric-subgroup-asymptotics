import SymmetricSubgroupAsymptotics.CFSGFFourE6NegativeRootUnits
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckPositivePGroup
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHeight

/-! Both signed folded root subgroups lie in the literal corresponding
E6 unipotent subgroups, and together generate the actual F4 matrix group.
In defining characteristic they are p-groups by this actual inclusion. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6RootSubgroups
open CFSGFFourSerreMatrices CFSGFFourE6PositiveRootUnits CFSGFFourE6NegativeRootUnits
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGSerreQuadraticMatrix CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoCoordinateHeight

def foldedRootGroup (K : Type) [Field K] (neg : Bool) :
    Subgroup ((Matrix Index Index K)ˣ) :=
  Subgroup.closure (Set.range (fun z : Fin 4×K=>canonicalRoot realizationData K neg z.1 z.2))

theorem folded_root_mem (K : Type) [Field K] (neg : Bool) (i : Fin 4) (t : K) :
    canonicalRoot realizationData K neg i t∈foldedRootGroup K neg :=
  Subgroup.subset_closure ⟨(i,t),rfl⟩

theorem foldedRootGroup_le_ambient (K : Type) [Field K] (neg : Bool) :
    foldedRootGroup K neg≤rootGroup CartanMatrix.E₆ CartanMatrix.E₆_transpose
      E6_positive_definite E6Base E6Index K neg := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨⟨i,t⟩,rfl⟩
  change canonicalRoot realizationData K neg i t∈rootGroup CartanMatrix.E₆
    CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K neg
  have he6 (j : Fin 6) : canonicalRoot e6Data K neg j t∈
      rootGroup CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K neg :=
    Subgroup.subset_closure ⟨(j,t),rfl⟩
  cases neg
  · rw [folded_positive_root]
    fin_cases i
    · exact (rootGroup CartanMatrix.E₆ CartanMatrix.E₆_transpose
        E6_positive_definite E6Base E6Index K false).mul_mem (he6 0) (he6 5)
    · exact (rootGroup CartanMatrix.E₆ CartanMatrix.E₆_transpose
        E6_positive_definite E6Base E6Index K false).mul_mem (he6 2) (he6 4)
    · exact he6 3
    · exact he6 1
  · rw [folded_negative_root]
    fin_cases i
    · exact (rootGroup CartanMatrix.E₆ CartanMatrix.E₆_transpose
        E6_positive_definite E6Base E6Index K true).mul_mem (he6 0) (he6 5)
    · exact (rootGroup CartanMatrix.E₆ CartanMatrix.E₆_transpose
        E6_positive_definite E6Base E6Index K true).mul_mem (he6 2) (he6 4)
    · exact he6 3
    · exact he6 1

theorem foldedRootGroup_le_model (K : Type) [Field K] (neg : Bool) :
    foldedRootGroup K neg≤canonicalElementaryGroup realizationData K := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨⟨i,t⟩,rfl⟩
  exact Subgroup.subset_closure ⟨neg,i,t,rfl⟩

theorem foldedRootGroup_sup (K : Type) [Field K] :
    foldedRootGroup K false⊔foldedRootGroup K true=
      canonicalElementaryGroup realizationData K := by
  apply le_antisymm (sup_le (foldedRootGroup_le_model K false) (foldedRootGroup_le_model K true))
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨neg,i,t,rfl⟩
  cases neg
  · exact (show foldedRootGroup K false≤foldedRootGroup K false⊔foldedRootGroup K true
      from le_sup_left) (folded_root_mem K false i t)
  · exact (show foldedRootGroup K true≤foldedRootGroup K false⊔foldedRootGroup K true
      from le_sup_right) (folded_root_mem K true i t)

theorem foldedModel_le_ambient (K : Type) [Field K] :
    canonicalElementaryGroup realizationData K≤canonicalElementaryGroup e6Data K := by
  rw [←foldedRootGroup_sup,←positive_sup_negative CartanMatrix.E₆ CartanMatrix.E₆_transpose
    E6_positive_definite E6Base E6Index K]
  exact sup_le_sup (foldedRootGroup_le_ambient K false) (foldedRootGroup_le_ambient K true)

theorem foldedRootGroup_isPGroup (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (neg : Bool) : IsPGroup p (foldedRootGroup K neg) := by
  have hamb : IsPGroup p (rootGroup CartanMatrix.E₆ CartanMatrix.E₆_transpose
      E6_positive_definite E6Base E6Index K neg) := by
    cases neg
    · exact positive_isPGroup CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
        E6Base E6Index coordinateHeight
        (simple_height CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
          E6_positive_definite CartanMatrix.E₆_off_diag_nonpos) K p
    · exact negative_isPGroup CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
        E6Base E6Index coordinateHeight
        (simple_height CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
          E6_positive_definite CartanMatrix.E₆_off_diag_nonpos) K p
  exact hamb.of_injective (Subgroup.inclusion (foldedRootGroup_le_ambient K neg))
    (Subgroup.inclusion_injective _)

end SymmetricSubgroupAsymptotics.CFSGFFourE6RootSubgroups
