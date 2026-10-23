import SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortComplement
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortParameterWeyl
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckLongA2Commutator
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! An actual complement factorization of U at the folded short simple
orbit. The three outer simple-root groups commute; the remaining root
tail is normal in U. The factorization uses actual subgroup generation
and normality, independently of the coefficient-field characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Pointwise
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortComplementFactor
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckPositiveTwist CFSGTrialityGeckShortComplement
open CFSGTrialityGeckShortParameterWeyl CFSGTrialityGeckLongA2Commutator
open CFSGTrialityGeckFixedRootSections CFSGTrialityD4PositiveRootOrbits
open CFSGTrialityFixedWeylWords CFSGSerreQuadraticMatrix
open CFSGNormTwoCoordinateFunctionalRootTail CFSGGradedMatrixSubgroups

def outerRootHom (K : Type) [Field K] (i : Fin 3) :
    Multiplicative K →* (Matrix GeckIndex GeckIndex K)ˣ where
  toFun t := canonicalRoot rawData K false (outerNode i) t.toAdd
  map_one' := canonicalRoot_zero rawData K false (outerNode i)
  map_mul' a b := (canonicalRoot_add rawData K false (outerNode i) a.toAdd b.toAdd).symm

def outerProductHom (K : Type) [Field K] :
    (Fin 3 → Multiplicative K) →* (Matrix GeckIndex GeckIndex K)ˣ :=
  MonoidHom.noncommPiCoprod (outerRootHom K)
    (fun i j hij a b => CFSGTrialityGeckShortParameterWeyl.outer_roots_commute
      K i j hij false false a.toAdd b.toAdd)

abbrev outerGroup (K : Type) [Field K] := (outerProductHom K).range

theorem outer_root_mem (K : Type) [Field K] (i : Fin 3) (t : K) :
    canonicalRoot rawData K false (outerNode i) t ∈ outerGroup K := by
  have hle : (outerRootHom K i).range ≤ outerGroup K := by
    change (outerRootHom K i).range ≤ (outerProductHom K).range
    rw [outerProductHom, MonoidHom.noncommPiCoprod_range]
    exact le_iSup (fun j => (outerRootHom K j).range) i
  exact hle ⟨Multiplicative.ofAdd t, rfl⟩

theorem outerGroup_le_positive (K : Type) [Field K] : outerGroup K ≤ Positive K := by
  change (outerProductHom K).range ≤ Positive K
  rw [outerProductHom, MonoidHom.noncommPiCoprod_range]
  apply iSup_le
  intro i
  rintro x ⟨t, rfl⟩
  exact Subgroup.subset_closure ⟨(outerNode i, t.toAdd), rfl⟩

theorem central_root_mem_shortComplement (K : Type) [Field K] (t : K) :
    canonicalRoot rawData K false 1 t ∈ shortComplement K := by
  obtain ⟨ε, _, he⟩ := longSection_selected_sign 0
  have he0 : canonicalRoot rawData K false 1 t =
      CFSGNormTwoCoordinateSelectedRootElement.selectedRootElement (CartanMatrix.D 4)
        (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4) D4_positive_definite
        (CartanMatrix.D_off_diag_nonpos 4) K (longRoot 0) ((ε : K) * t) := by
    simpa only [longSection, longTransport, Matrix.cons_val_zero, one_mul, inv_one, mul_one]
      using he K t
  rw [he0]
  exact root_mem_functionalTail (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
    K (LinearMap.proj 1) 1 (longRoot 0) (long_positive 0) (by decide) ((ε : K) * t)

theorem shortComplement_sup_outer (K : Type) [Field K] :
    shortComplement K ⊔ outerGroup K = Positive K := by
  apply le_antisymm (sup_le (shortComplement_le_positive K) (outerGroup_le_positive K))
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨⟨i, t⟩, rfl⟩
  fin_cases i
  · exact (show outerGroup K ≤ shortComplement K ⊔ outerGroup K from le_sup_right)
      (outer_root_mem K 0 t)
  · exact (show shortComplement K ≤ shortComplement K ⊔ outerGroup K from le_sup_left)
      (central_root_mem_shortComplement K t)
  · exact (show outerGroup K ≤ shortComplement K ⊔ outerGroup K from le_sup_right)
      (outer_root_mem K 1 t)
  · exact (show outerGroup K ≤ shortComplement K ⊔ outerGroup K from le_sup_right)
      (outer_root_mem K 2 t)

theorem positive_short_factor (K : Type) [Field K]
    (u : (Matrix GeckIndex GeckIndex K)ˣ) (hu : u ∈ Positive K) :
    ∃ c ∈ shortComplement K, ∃ a : Fin 3 → Multiplicative K, u = c * outerProductHom K a := by
  have hN : outerGroup K ≤ Subgroup.normalizer
      (shortComplement K : Set (Matrix GeckIndex GeckIndex K)ˣ) :=
    (outerGroup_le_positive K).trans (positive_le_normalizer_shortComplement K)
  have hm := Subgroup.coe_mul_of_right_le_normalizer_left (shortComplement K) (outerGroup K) hN
  rw [← shortComplement_sup_outer K] at hu
  change u ∈ ((shortComplement K ⊔ outerGroup K :
    Subgroup (Matrix GeckIndex GeckIndex K)ˣ) : Set (Matrix GeckIndex GeckIndex K)ˣ) at hu
  rw [hm] at hu
  obtain ⟨c, hc, o, ho, he⟩ := hu
  obtain ⟨a, ha⟩ := ho
  exact ⟨c, hc, a, by rw [ha]; exact he.symm⟩

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortComplementFactor
