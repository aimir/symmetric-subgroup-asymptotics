import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRootSubgroupTwist
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootHeightFiltration
import Mathlib.Algebra.Group.Subgroup.Finite

/-! Every ACTUAL positive height tail is stable under the literal E6
diagram--field matrix twist. Root labels and integer height, rather than
field-valued torus weights or an invariant total ordering, prove this. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckHeightTwist
open CFSGNormTwoRootPairing CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite CFSGSerreDiagram
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6GeckRootSubgroupTwist CFSGNormTwoCartanDiagramRoots
open CFSGNormTwoCartanDiagramWords CFSGNormTwoCoordinateRootSubgroup
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateRootElementRange
open CFSGNormTwoCoordinateRootHeightFiltration CFSGIntegerHeightSign

abbrev HeightTail (K : Type) [Field K] (h : ℤ) :=
  heightTail CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K h

theorem selected_twist_mem_heightTail (K : Type) [Field K] (σ : K ≃+* K)
    (h : ℤ) (k : Roots CartanMatrix.E₆) (hk : ∀ i, 0 ≤ k.val i)
    (hh : h ≤ height k.val) (a : K) :
    unitTwist K σ (selectedRootElement CartanMatrix.E₆ CartanMatrix.E₆_diag
      CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos
      K k a) ∈ HeightTail K h := by
  let θ := rootPermutation CartanMatrix.E₆ e6Permutation e6_preserves k
  have hm : unitTwist K σ (selectedRootElement CartanMatrix.E₆ CartanMatrix.E₆_diag
      CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos
      K k a) ∈ rootSubgroup CartanMatrix.E₆ CartanMatrix.E₆_diag
        CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos
        K θ := by
    dsimp only [θ]
    rw [← root_subgroup_twist K σ k]
    exact ⟨_, selectedRootElement_mem CartanMatrix.E₆ CartanMatrix.E₆_diag
      CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos
      K k a, rfl⟩
  obtain ⟨b, hb⟩ := (mem_rootSubgroup_iff_selected CartanMatrix.E₆
    CartanMatrix.E₆_diag CartanMatrix.E₆_transpose E6_positive_definite
    CartanMatrix.E₆_off_diag_nonpos K θ _).mp hm
  rw [← hb]
  apply rootElement_mem_heightTail CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos
    K h θ
  · exact rootPermutation_positive CartanMatrix.E₆ e6Permutation e6_preserves k hk
  · change h ≤ height (rootPermutation CartanMatrix.E₆ e6Permutation e6_preserves k).val
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

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckHeightTwist
