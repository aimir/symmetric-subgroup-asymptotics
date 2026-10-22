import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateComplementKernel
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootPositiveContainment
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootLeadingAxes

/-! Exactly the positive lattice root groups other than the excluded
simple root lie in the literal positive complement. This is proved from
actual parameter ranges, not assumed as a root-group factorization. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateComplementRoots
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoGeckPositiveComplement CFSGNormTwoCoordinateComplementKernel
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCoordinateRootElementRange
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateRootPositiveContainment
open CFSGNormTwoCoordinatePositiveRootGenerators CFSGNormTwoCoordinateRootLeadingAxes
open CFSGNormTwoCoordinateLeadingFactor CFSGNormTwoCoordinateRootHeightQuotient
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "M" => positiveComplement A hs hp b₀ s₀ K

theorem rootSubgroup_le_complement_iff (i : Fin r) (k : Roots A) :
    rootSubgroup A hd hs hp ho K k≤M i↔(∀j,0≤k.val j) ∧ k≠(s₀ i : Roots A) := by
  classical
  constructor
  · intro hk
    refine ⟨(rootSubgroup_le_positive_iff A hd hs hp ho K k).mp
      (hk.trans (complement_le_positive A hs hp b₀ s₀ K i)),?_⟩
    intro he
    subst k
    obtain ⟨ε,hε,hroot⟩ := leading_selected_simple A hd hs hp ho i
    have hz := complement_leading_zero A hd hs hp ho K i
      (selectedRootElement A hd hs hp ho K (s₀ i) 1)
      (hk (selectedRootElement_mem A hd hs hp ho K (s₀ i) 1))
    rw [hroot K 1] at hz
    rcases hε with rfl|rfl <;> norm_num [Pi.single_apply] at hz
  · rintro ⟨hk,hki⟩ x hx
    obtain ⟨a,rfl⟩ := (mem_rootSubgroup_iff_selected A hd hs hp ho K k x).mp hx
    have hu : selectedRootElement A hd hs hp ho K k a∈PositiveGroup A hd hs hp ho K :=
      positive_root_subgroup_le A hd hs hp ho K k hk
        (selectedRootElement_mem A hd hs hp ho K k a)
    apply (positive_mem_complement_iff_leading_zero A hd hs hp ho K i ⟨_,hu⟩).mpr
    by_cases hsimp : ∃j : Fin r,k=(s₀ j : Roots A)
    · obtain ⟨j,rfl⟩ := hsimp
      have hij : i≠j := by
        intro h
        subst j
        exact hki rfl
      obtain ⟨ε,hε,hroot⟩ := leading_selected_simple A hd hs hp ho j
      rw [hroot K a]
      simp [Pi.single_apply,hij,Ne.symm hij]
    · rw [leading_selected_nonsimple A hd hs hp ho K k
        (fun j hj=>hsimp ⟨j,hj⟩) a]
      rfl

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateComplementRoots
