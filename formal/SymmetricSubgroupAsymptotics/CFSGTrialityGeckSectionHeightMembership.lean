import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSectionRootLabels
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckHeightTwist
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCanonicalSimpleRootLine
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootWeylAction

/-! The displayed fixed triality sections lie in the claimed ACTUAL
positive height tails. Each conjugated factor is first placed in its
proved original lattice root subgroup, then in the checked height closure. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckSectionHeightMembership
open CFSGNormTwoRootPairing CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckFixedRootWords CFSGTrialityGeckFixedRootSections
open CFSGTrialityGeckSectionRootLabels CFSGTrialityGeckHeightTwist
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCoordinateRootElementRange
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateRootHeightFiltration
open CFSGNormTwoCoordinateCanonicalSimpleRootLine CFSGNormTwoCoordinateRootWeylAction
open CFSGTrialityD4PositiveRootOrbits CFSGTrialityD4PositiveRootIndex CFSGIntegerHeightSign

abbrev RootLine (K : Type) [Field K] (k : Roots (CartanMatrix.D 4)) :=
  rootSubgroup (CartanMatrix.D 4) (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K k

private theorem simple_mem (K : Type) [Field K] (j : Fin 4) (t : K) :
    canonicalRoot rawData K false j t ∈ RootLine K (Index j) := by
  have h := rootSubgroup_simple_eq_canonical (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K j
  change RootLine K (Index j) = canonicalRootSubgroup rawData K false j at h
  rw [h]
  exact ⟨t, rfl⟩

private theorem conjugate_mem (K : Type) [Field K] (w : List (Fin 4))
    (k : Roots (CartanMatrix.D 4)) (x : (Matrix GeckIndex GeckIndex K)ˣ)
    (hx : x ∈ RootLine K k) :
    canonicalWord rawData K w * x * (canonicalWord rawData K w)⁻¹ ∈
      RootLine K (CFSGTrialityD4RelativeRootWords.rootWord w k) := by
  have hm : canonicalWord rawData K w * x * (canonicalWord rawData K w)⁻¹ ∈
      (RootLine K k).map (MulAut.conj (canonicalWord rawData K w)).toMonoidHom :=
    ⟨x, hx, rfl⟩
  have he := rootSubgroup_map_word (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K w k
  change (RootLine K k).map (MulAut.conj (canonicalWord rawData K w)).toMonoidHom =
    RootLine K (CFSGTrialityD4RelativeRootWords.rootWord w k) at he
  rw [he] at hm
  exact hm

def shortFactor (K : Type) [CommRing K] (s k : Fin 3) (t : K) :=
  shortTransport K s * canonicalRoot rawData K false (CFSGTrialityFixedWeylWords.outerNode k) t *
    (shortTransport K s)⁻¹

theorem shortFactor_mem_root (K : Type) [Field K] (s k : Fin 3) (t : K) :
    shortFactor K s k t ∈ RootLine K (shortLabel s k) := by
  unfold shortFactor
  rw [shortTransport_word]
  have hx : canonicalRoot rawData K false (CFSGTrialityFixedWeylWords.outerNode k) t ∈
      RootLine K (shortRoot 0 k) := by
    rw [short_seed_index]
    exact simple_mem K _ t
  have hm := conjugate_mem K (shortWord s) (shortRoot 0 k) _ hx
  rw [short_word_label] at hm
  exact hm

theorem longSection_mem_root (K : Type) [Field K] (s : Fin 3) (t : K) :
    longSection K s false t ∈ RootLine K (longRoot s) := by
  unfold longSection
  rw [longTransport_word]
  have hx : canonicalRoot rawData K false 1 t ∈ RootLine K (longRoot 0) := by
    rw [long_seed_index]
    exact simple_mem K 1 t
  have hm := conjugate_mem K (longWord s) (longRoot 0) _ hx
  rw [long_word_label] at hm
  exact hm

private theorem root_mem_tail (K : Type) [Field K] (h : ℤ)
    (k : Roots (CartanMatrix.D 4)) (hk : ∀ i, 0 ≤ k.val i) (hh : h ≤ height k.val)
    (x : (Matrix GeckIndex GeckIndex K)ˣ) (hx : x ∈ RootLine K k) : x ∈ HeightTail K h := by
  obtain ⟨a, rfl⟩ := (mem_rootSubgroup_iff_selected (CartanMatrix.D 4)
    (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4) D4_positive_definite
    (CartanMatrix.D_off_diag_nonpos 4) K k x).mp hx
  exact rootElement_mem_heightTail (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
    K h k hk hh a

theorem shortFactor_mem_heightTail (K : Type) [Field K] (s k : Fin 3) (t : K) :
    shortFactor K s k t ∈ HeightTail K (![(1 : ℤ),2,3] s) :=
  root_mem_tail K _ (shortLabel s k) (short_label_positive s k)
    (short_label_height s k).symm.le _ (shortFactor_mem_root K s k t)

theorem longSection_mem_heightTail (K : Type) [Field K] (s : Fin 3) (t : K) :
    longSection K s false t ∈ HeightTail K (![(1 : ℤ),4,5] s) :=
  root_mem_tail K _ (longRoot s) (long_positive s) (long_height s).symm.le _
    (longSection_mem_root K s t)

theorem shortSection_mem_heightTail (K : Type) [Field K] (σ : K ≃+* K)
    (s : Fin 3) (t : K) : shortSection K σ s false t ∈ HeightTail K (![(1 : ℤ),2,3] s) := by
  have he : shortSection K σ s false t =
      shortFactor K s 0 t * shortFactor K s 1 (σ t) * shortFactor K s 2 (σ (σ t)) := by
    dsimp only [shortSection, shortOrbit, shortFactor]
    group <;> rfl
  rw [he]
  exact (HeightTail K _).mul_mem
    ((HeightTail K _).mul_mem (shortFactor_mem_heightTail K s 0 t)
      (shortFactor_mem_heightTail K s 1 (σ t)))
    (shortFactor_mem_heightTail K s 2 (σ (σ t)))

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckSectionHeightMembership
