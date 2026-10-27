import SymmetricSubgroupAsymptotics.CFSGNormTwoOriginalSourceFamily
import SymmetricSubgroupAsymptotics.CFSGExceptionalNormTwoBases
import SymmetricSubgroupAsymptotics.CFSGE6FiniteRootMenu
import SymmetricSubgroupAsymptotics.CFSGE6PositiveRootLowerWitness

/-! A concrete 78-element family in the ORIGINAL E6 integral Serre lattice.
The 36 positive roots are the exact actual norm-two positive roots: the
existing checked upper menu and lower witness give equality. Source words
are constructed from genuine smaller positive parents, not matrix lifts.
No claim of source spanning/independence or source faithfulness is made. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGE6OriginalSourceCandidates
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGNormTwoOriginalPositiveSources
open CFSGNormTwoOriginalSourceFamily CFSGExceptionalCartanPositiveDefinite

abbrev Index := BasisIndex CartanMatrix.E₆

def originalVector : Index→integralLattice CartanMatrix.E₆ :=
  vector CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose E6_positive_definite

theorem positive_root_card : Nat.card (Positive CartanMatrix.E₆)=36 := by
  apply le_antisymm
  · exact CFSGE6FiniteRootMenu.positive_roots_card_le
  · exact CFSGE6PositiveRootLowerWitness.positive_root_card_lower

theorem index_card : Nat.card Index=78 := by
  change Nat.card (Fin 6 ⊕ (Bool×Positive CartanMatrix.E₆))=78
  rw [Nat.card_sum,Nat.card_prod,positive_root_card]
  norm_num

theorem generators_mem (g : CartanMatrix.Generators (Fin 6)) :
    latticeGenerator CartanMatrix.E₆ g∈Submodule.span ℤ (Set.range originalVector) :=
  CFSGNormTwoOriginalSourceFamily.generators_mem CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite g

theorem source_weight (neg : Bool) (k : Positive CartanMatrix.E₆) (a : Fin 6) :
    ⁅CFSGSerreSignedRootWeights.coroot CartanMatrix.E₆ neg a,
      (originalVector (.inr (neg,k))).val⁆=
        weight CartanMatrix.E₆ a k • (originalVector (.inr (neg,k))).val :=
  CFSGNormTwoOriginalPositiveSources.source_weight CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite neg k a

theorem positive_comparison (i : Fin 6) (k : Positive CartanMatrix.E₆) :
    ∃a,0<(CartanMatrix.E₆ a i:ℚ)+weight CartanMatrix.E₆ a k :=
  CFSGNormTwoOriginalSourceFamily.positive_comparison CartanMatrix.E₆
    CartanMatrix.E₆_transpose E6_positive_definite i k

end SymmetricSubgroupAsymptotics.CFSGE6OriginalSourceCandidates
