import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootSupportCardinality
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootPairCommute
import Mathlib.GroupTheory.Subgroup.Centralizer

/-! A genuine centralizer-cardinality lower bound for every original
lattice-labelled root subgroup, including negative roots. Independent
normal words on the positive roots of pairing zero or one centralize
the target subgroup. The count is symbolic, with no exceptional census. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootCentralizerCardinality
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCoordinateRootElementRange
open CFSGNormTwoCoordinateRootHeightQuotient CFSGNormTwoCoordinatePositiveRootGenerators
open CFSGNormTwoCoordinateRootSupportCardinality CFSGNormTwoCoordinateRootPairCommute
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

def commutingPositiveRoots (k : Roots A) : Finset (PositiveRoot A) := by
  classical
  exact Finset.univ.filter (fun l : PositiveRoot A=>
    integerPairing A l.val.val k.val=0 ∨ integerPairing A l.val.val k.val=1)

def positiveRootCentralizer (K : Type) [Field K] (k : Roots A) :
    Subgroup (PositiveGroup A hd hs hp ho K) :=
  (Subgroup.centralizer (rootSubgroup A hd hs hp ho K k : Set _)).subgroupOf
    (PositiveGroup A hd hs hp ho K)

theorem root_parameter_mem_centralizer (K : Type) [Field K] (k : Roots A) (l : PositiveRoot A)
    (hpair : integerPairing A l.val.val k.val=0 ∨ integerPairing A l.val.val k.val=1)
    (a : Multiplicative K) :
    positiveRootParameterHom A hd hs hp ho K l.val l.property a∈
      positiveRootCentralizer A hd hs hp ho K k := by
  change CFSGNormTwoCoordinateSelectedRootElement.selectedRootElement A hd hs hp ho K l.val a.toAdd∈
    Subgroup.centralizer (rootSubgroup A hd hs hp ho K k : Set _)
  apply Subgroup.mem_centralizer_iff.mpr
  intro x hx
  obtain ⟨b,rfl⟩ := (mem_rootSubgroup_iff_selected A hd hs hp ho K k x).mp hx
  exact (pair_commute A hd hs hp ho K l.val k hpair a.toAdd b).eq.symm

theorem positive_root_centralizer_card_lower (K : Type) [Field K] [Finite K] (k : Roots A) :
    Nat.card K ^ (commutingPositiveRoots A k).card≤
      Nat.card (positiveRootCentralizer A hd hs hp ho K k) := by
  classical
  apply root_support_card_le A hd hs hp ho K (commutingPositiveRoots A k)
    (positiveRootCentralizer A hd hs hp ho K k)
  intro l a
  have hl := (Finset.mem_filter.mp l.property).2
  exact root_parameter_mem_centralizer A hd hs hp ho K k l.val hl a

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootCentralizerCardinality
