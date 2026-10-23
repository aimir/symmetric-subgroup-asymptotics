import SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortComplementUnique
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRootSubgroupTwist

/-! The short complement and outer subgroup are genuinely twist-stable.
Their proved unique factorization therefore yields genuinely fixed
factors for every fixed U element. No fixed-point surjectivity through
a quotient or product is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortComplementFixedFactor
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckShortComplement CFSGTrialityGeckShortComplementFactor
open CFSGTrialityGeckShortComplementUnique CFSGTrialityGeckMatrixTwist
open CFSGTrialityGeckRootSubgroupTwist CFSGTrialityGeckPositiveTwist
open CFSGNormTwoRootPairing CFSGNormTwoCoordinateRootSubgroup
open CFSGNormTwoCoordinateRootElementRange CFSGNormTwoCoordinateSelectedRootElement
open CFSGNormTwoCoordinateFunctionalRootTail CFSGNormTwoCartanDiagramRoots
open CFSGTrialityD4PositiveRootOrbits CFSGTrialityFixedWeylWords CFSGSerreDiagram

theorem rootSubgroup_le_shortComplement (K : Type) [Field K]
    (k : Roots (CartanMatrix.D 4)) (hk : ∀ i, 0 ≤ k.val i) (hc : 1 ≤ k.val 1) :
    rootSubgroup (CartanMatrix.D 4) (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K k ≤ shortComplement K := by
  intro x hx
  obtain ⟨a, rfl⟩ := (mem_rootSubgroup_iff_selected (CartanMatrix.D 4)
    (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4) D4_positive_definite
    (CartanMatrix.D_off_diag_nonpos 4) K k x).mp hx
  exact root_mem_functionalTail (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
    K (LinearMap.proj 1) 1 k hk hc a

theorem shortComplement_twist_le (K : Type) [Field K] (σ : K ≃+* K) :
    (shortComplement K).map (unitTwist K σ).toMonoidHom ≤ shortComplement K := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨k, hk, a, rfl⟩
  let k' := rootPermutation (CartanMatrix.D 4) trialityPermutation triality_preserves k.val
  have hkp : ∀ i, 0 ≤ k'.val i := by
    intro i
    exact k.property (trialityPermutation.symm i)
  have hkc : 1 ≤ k'.val 1 := by
    change 1 ≤ k.val.val (trialityPermutation.symm 1)
    have hi : trialityPermutation.symm (1 : Fin 4) = 1 := by
      rw [triality_symm_apply]
      rfl
    rw [hi]
    exact hk
  apply rootSubgroup_le_shortComplement K k' hkp hkc
  dsimp only [k']
  rw [← root_subgroup_twist K σ k.val]
  refine ⟨selectedRootElement (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
    K k.val a, ?_, rfl⟩
  exact (mem_rootSubgroup_iff_selected (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
    K k.val _).mpr ⟨a, rfl⟩

theorem outer_triality_node (i : Fin 3) :
    trialityPermutation (outerNode i) = outerNode (cycle i) := by
  fin_cases i <;> rfl

theorem outerGroup_twist_le (K : Type) [Field K] (σ : K ≃+* K) :
    (outerGroup K).map (unitTwist K σ).toMonoidHom ≤ outerGroup K := by
  apply Subgroup.map_le_iff_le_comap.mpr
  change (outerProductHom K).range ≤ _
  rw [outerProductHom, MonoidHom.noncommPiCoprod_range]
  apply iSup_le
  intro i
  rintro x ⟨t, rfl⟩
  change unitTwist K σ (CFSGSerreQuadraticMatrix.canonicalRoot rawData K false
    (outerNode i) t.toAdd) ∈ outerGroup K
  rw [unitTwist_raw_root, outer_triality_node]
  exact outer_root_mem K (cycle i) (σ t.toAdd)

theorem exists_fixed_short_factors (K : Type) [Field K] (σ : K ≃+* K)
    (u : (Matrix GeckIndex GeckIndex K)ˣ) (hu : u ∈ Positive K)
    (hfix : unitTwist K σ u = u) :
    ∃ c ∈ shortComplement K, ∃ o ∈ outerGroup K,
      unitTwist K σ c = c ∧ unitTwist K σ o = o ∧ u = c * o := by
  obtain ⟨c, hc, a, he⟩ := positive_short_factor K u hu
  let o := outerProductHom K a
  have ho : o ∈ outerGroup K := ⟨a, rfl⟩
  have hc' : unitTwist K σ c ∈ shortComplement K := shortComplement_twist_le K σ ⟨c, hc, rfl⟩
  have ho' : unitTwist K σ o ∈ outerGroup K := outerGroup_twist_le K σ ⟨o, ho, rfl⟩
  have he' : unitTwist K σ c * unitTwist K σ o = c * o := by
    rw [← map_mul]
    change unitTwist K σ (c * outerProductHom K a) = c * outerProductHom K a
    rw [← he, hfix]
  obtain ⟨hcfix, hofix⟩ := short_factor_unique K (unitTwist K σ c) c
    (unitTwist K σ o) o hc' hc ho' ho he'
  exact ⟨c, hc, o, ho, hcfix, hofix, he⟩

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortComplementFixedFactor
