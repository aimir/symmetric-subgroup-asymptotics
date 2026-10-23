import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRootSubgroupTwist
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootHeightFiltration
import Mathlib.Algebra.Group.Subgroup.Finite

/-! Every ACTUAL positive height tail is stable under the literal D4
diagram--field matrix twist. Root labels and integer height, rather than
field-valued torus weights or an invariant total ordering, prove this. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckHeightTwist
open CFSGNormTwoRootPairing CFSGTrialityD4NormTwo CFSGSerreDiagram
open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckMatrixTwist
open CFSGTrialityGeckRootSubgroupTwist CFSGNormTwoCartanDiagramRoots
open CFSGNormTwoCartanDiagramWords CFSGNormTwoCoordinateRootSubgroup
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateRootElementRange
open CFSGNormTwoCoordinateRootHeightFiltration CFSGIntegerHeightSign

abbrev HeightTail (K : Type) [Field K] (h : ℤ) :=
  heightTail (CartanMatrix.D 4) (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K h

theorem selected_twist_mem_heightTail (K : Type) [Field K] (σ : K ≃+* K)
    (h : ℤ) (k : Roots (CartanMatrix.D 4)) (hk : ∀ i, 0 ≤ k.val i)
    (hh : h ≤ height k.val) (a : K) :
    unitTwist K σ (selectedRootElement (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
      (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
      K k a) ∈ HeightTail K h := by
  let θ := rootPermutation (CartanMatrix.D 4) trialityPermutation triality_preserves k
  have hm : unitTwist K σ (selectedRootElement (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
      (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
      K k a) ∈ rootSubgroup (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
        (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
        K θ := by
    dsimp only [θ]
    rw [← root_subgroup_twist K σ k]
    exact ⟨_, selectedRootElement_mem (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
      (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
      K k a, rfl⟩
  obtain ⟨b, hb⟩ := (mem_rootSubgroup_iff_selected (CartanMatrix.D 4)
    (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4) D4_positive_definite
    (CartanMatrix.D_off_diag_nonpos 4) K θ _).mp hm
  rw [← hb]
  apply rootElement_mem_heightTail (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
    K h θ
  · exact rootPermutation_positive (CartanMatrix.D 4) trialityPermutation triality_preserves k hk
  · change h ≤ height (rootPermutation (CartanMatrix.D 4) trialityPermutation triality_preserves k).val
    rw [rootPermutation_height]
    exact hh

theorem heightTail_twist_le (K : Type) [Field K] (σ : K ≃+* K) (h : ℤ) :
    (HeightTail K h).map (unitTwist K σ).toMonoidHom ≤ HeightTail K h := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨k, hk, a, rfl⟩
  exact selected_twist_mem_heightTail K σ h k.val k.property hk a

theorem heightTail_twist (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (h : ℤ) :
    (HeightTail K h).map (unitTwist K σ).toMonoidHom = HeightTail K h := by
  apply Subgroup.eq_of_le_of_card_ge (heightTail_twist_le K σ h)
  exact (Nat.card_congr ((unitTwist K σ).subgroupMap (HeightTail K h)).toEquiv).le

def heightTailTwist (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (h : ℤ) :
    MulAut (HeightTail K h) :=
  ((unitTwist K σ).subgroupMap (HeightTail K h)).trans
    (MulEquiv.subgroupCongr (heightTail_twist K σ h))

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckHeightTwist
