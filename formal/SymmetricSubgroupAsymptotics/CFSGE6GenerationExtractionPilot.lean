import SymmetricSubgroupAsymptotics.CFSGE6GenerationTorusPilot
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCommutingRoots
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRationalAdjointStrings
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationScalarFilter

/-! One actual E6 two-element extraction pilot. For every finite field
with at least three elements, a primitive torus word and a fixed root/
Coxeter word recover the entire fifth simple-root line. This does not
assert that the two words already generate the whole E6 model. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGE6GenerationExtractionPilot
open CFSGE6GenerationTorusPilot CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGSerreQuadraticMatrix
open CFSGNormTwoRootPairing CFSGNormTwoGeckIntegralRealization
open CFSGOrthogonalDGenerationScalarFilter
local instance : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _

theorem zero_five_commute (K : Type) [Field K] (a b : K) :
    Commute (root K 0 a) (root K 5 b) := by
  apply CFSGSerreQuadraticCommutingRoots.roots_commute
  exact CFSGNormTwoGeckRationalAdjointStrings.lie_of_cartan_zero
    CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index 0 5
    (by rw [E6_cartan]; decide)

def secondGenerator (K : Type) [Field K] : Ambient K :=
  root K 0 1*root K 5 1*coxeter K

def cleanedGenerator (K : Type) [Field K] : Ambient K := root K 0 1*coxeter K

def pairGroup (K : Type) [Field K] (g : Kˣ) : Subgroup (Ambient K) :=
  Subgroup.closure ({torus K g,secondGenerator K} : Set (Ambient K))

theorem secondGenerator_mem_canonical (K : Type) [Field K] :
    secondGenerator K∈canonicalElementaryGroup e6Data K := by
  exact (canonicalElementaryGroup e6Data K).mul_mem
    ((canonicalElementaryGroup e6Data K).mul_mem
      (root_mem_canonical K 0 1) (root_mem_canonical K 5 1))
    (coxeter_mem_canonical K)

theorem pairGroup_le_canonical (K : Type) [Field K] (g : Kˣ) :
    pairGroup K g≤canonicalElementaryGroup e6Data K := by
  apply (Subgroup.closure_le _).mpr
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl|hx
  · exact torus_mem_canonical K g
  · rcases Set.mem_singleton_iff.mp hx with rfl
    exact secondGenerator_mem_canonical K

theorem fifth_line_of_pair (K : Type) [Field K] [Finite K]
    (hcard : 3≤Nat.card K) (g : Kˣ) (hg : ∀u : Kˣ,u∈Subgroup.zpowers g)
    (H : Subgroup (Ambient K)) (hT : torus K g∈H) (hy : secondGenerator K∈H) :
    ∀a : K,root K 5 a∈H := by
  exact second_line_of_pair hcard g hg (root K 0) (root K 5)
    (fun a b=>(canonicalRoot_add e6Data K false 0 a b).symm)
    (canonicalRoot_zero e6Data K false 0)
    (fun a b=>(canonicalRoot_add e6Data K false 5 a b).symm)
    (canonicalRoot_zero e6Data K false 5)
    (zero_five_commute K) (torus K g) (coxeter K) (g:K)⁻¹
    (torus_fixes_zero K g) (torus_scales_five K g)
    (conjugated_torus_scales_zero K g) (conjugated_torus_scales_five K g)
    (conjugated_torus_commutes K g) H hT hy

theorem cleanedGenerator_mem (K : Type) [Field K] [Finite K]
    (hcard : 3≤Nat.card K) (g : Kˣ) (hg : ∀u : Kˣ,u∈Subgroup.zpowers g)
    (H : Subgroup (Ambient K)) (hT : torus K g∈H) (hy : secondGenerator K∈H) :
    cleanedGenerator K∈H := by
  exact cleaned_word_mem (root K 0) (root K 5) (zero_five_commute K 1 1)
    (coxeter K) H (fifth_line_of_pair K hcard g hg H hT hy 1) hy

theorem pair_recovers_fifth_line (K : Type) [Field K] [Finite K]
    (hcard : 3≤Nat.card K) (g : Kˣ) (hg : ∀u : Kˣ,u∈Subgroup.zpowers g) :
    (∀a : K,root K 5 a∈pairGroup K g) ∧ cleanedGenerator K∈pairGroup K g := by
  have hT : torus K g∈pairGroup K g := Subgroup.subset_closure (by simp)
  have hy : secondGenerator K∈pairGroup K g := Subgroup.subset_closure (by simp)
  exact ⟨fifth_line_of_pair K hcard g hg _ hT hy,
    cleanedGenerator_mem K hcard g hg _ hT hy⟩

theorem exists_actual_pair_recovering_fifth_line (K : Type) [Field K] [Finite K]
    (hcard : 3≤Nat.card K) : ∃g : Kˣ,
    torus K g∈canonicalElementaryGroup e6Data K ∧
    secondGenerator K∈canonicalElementaryGroup e6Data K ∧
    (∀a : K,root K 5 a∈pairGroup K g) ∧ cleanedGenerator K∈pairGroup K g := by
  obtain ⟨g,hg⟩ := IsCyclic.exists_generator (α:=Kˣ)
  exact ⟨g,torus_mem_canonical K g,secondGenerator_mem_canonical K,
    pair_recovers_fifth_line K hcard g hg⟩

end SymmetricSubgroupAsymptotics.CFSGE6GenerationExtractionPilot
