import SymmetricSubgroupAsymptotics.CFSGAlternatingOrderThreeConjugacy
import SymmetricSubgroupAsymptotics.CFSGAlternatingThreeCyclePreservation
import SymmetricSubgroupAsymptotics.CFSGAutomorphismConjugacyClassAction
import SymmetricSubgroupAsymptotics.CFSGAlternatingStarRelations
import Mathlib.GroupTheory.Index

/-! The exceptional degree-six orbit consists of at most the single
and double three-cycle classes. Only two explicit point permutations
are used; no automorphism group is enumerated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGAlternatingSixConjugacyOrbit
open CFSGAlternatingStarGenerators CFSGAlternatingThreeCycleStars
open CFSGAlternatingOrderThreeConjugacy CFSGAlternatingThreeCyclePreservation
open CFSGAutomorphismConjugacyClassAction

abbrev A6 := alternatingGroup (Fin 6)

def single : A6 := ⟨cycle 0 1 2,
  (cycle_isThreeCycle (0 : Fin 6) 1 2 (by decide) (by decide) (by decide)).mem_alternatingGroup⟩

def double : A6 := single*⟨cycle 3 4 5,
  (cycle_isThreeCycle (3 : Fin 6) 4 5 (by decide) (by decide) (by decide)).mem_alternatingGroup⟩

theorem single_isThreeCycle : single.val.IsThreeCycle :=
  cycle_isThreeCycle (0 : Fin 6) 1 2 (by decide) (by decide) (by decide)

theorem double_cycleType : double.val.cycleType={3,3} := by
  decide +kernel

/-- Every image of the single-three-cycle class is one of exactly the
two available order-three profiles, each an actual A6 conjugacy class. -/
theorem orbit_subset_pair :
    MulAction.orbit (MulAut A6) (ConjClasses.mk single) ⊆
      ({ConjClasses.mk single,ConjClasses.mk double} : Set (ConjClasses A6)) := by
  intro x hx
  obtain ⟨f,hf⟩ := MulAction.mem_orbit_iff.mp hx
  rw [←hf]
  change ConjClasses.mk (f single)∈({ConjClasses.mk single,ConjClasses.mk double} : Set (ConjClasses A6))
  rcases map_three_cycle_six_type f single single_isThreeCycle with hs|hd
  · left
    apply ConjClasses.mk_eq_mk_iff_isConj.mpr
    apply isConj_of_three_cycle_type 6 (by decide) (f single) single 1 (by decide)
    · simpa only [Multiset.replicate_one] using hs
    · simpa only [Multiset.replicate_one] using single_isThreeCycle.cycleType
  · right
    apply Set.mem_singleton_iff.mpr
    apply ConjClasses.mk_eq_mk_iff_isConj.mpr
    apply isConj_of_three_cycle_type 6 (by decide) (f single) double 2 (by decide)
    · simpa only [Multiset.replicate_succ,Multiset.replicate_zero] using hd
    · simpa only [Multiset.replicate_succ,Multiset.replicate_zero] using double_cycleType

theorem conjugacy_stabilizer_index_le_two :
    (MulAction.stabilizer (MulAut A6) (ConjClasses.mk single)).index≤2 := by
  rw [MulAction.index_stabilizer]
  apply (Set.ncard_le_ncard orbit_subset_pair).trans
  exact (Set.ncard_insert_le _ _).trans (by simp)

end SymmetricSubgroupAsymptotics.CFSGAlternatingSixConjugacyOrbit
