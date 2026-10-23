import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRootSubgroupTwist
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateExcludedHeight
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLeadingHom

/-! The central simple node supplies the long relative rank-one factor.
The ordinary positive-complement factorization is unique by its integer
grading. Both factors are genuinely twist-stable, so a fixed positive
element factors through a fixed complement and a fixed field parameter.
This is a local factorization, not a cover of the whole fixed group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedLongComplementFactor
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckRootSubgroupTwist CFSGTrialityGeckMatrixTwist
open CFSGTrialityGeckPositiveTwist CFSGSerreDiagram CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckPositiveComplement CFSGNormTwoGeckComplementNormalizer
open CFSGNormTwoGeckComplementGrading CFSGNormTwoCoordinateExcludedHeight
open CFSGNormTwoGeckHeightSupport CFSGGradedMatrixSubgroups
open CFSGNormTwoCoordinateLeadingHom

abbrev longComplement (K : Type) [Field K] : Subgroup (Matrix GeckIndex GeckIndex K)ˣ :=
  positiveComplement (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index K 1

abbrev centralRootGroup (K : Type) [Field K] : Subgroup (Matrix GeckIndex GeckIndex K)ˣ :=
  canonicalRootSubgroup rawData K false 1

theorem longComplement_le_positive (K : Type) [Field K] :
    longComplement K ≤ Positive K :=
  complement_le_positive (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index K 1

theorem longWeyl_mem_normalizer_longComplement (K : Type) [Field K] :
    canonicalWeyl rawData K 1 ∈
      Subgroup.normalizer (longComplement K : Set ((Matrix GeckIndex GeckIndex K)ˣ)) :=
  weyl_mem_normalizer (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index K 1

theorem longComplement_inf_centralRoot (K : Type) [Field K] :
    longComplement K ⊓ centralRootGroup K = ⊥ := by
  have hC := complement_le_strict (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index (excludedHeight (1 : Fin 4)) 1
    (excluded_simple_zero (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
      (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) 1)
    (fun j hj => excluded_other_positive (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
      (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) 1 j hj) K
  have hR := simple_le_preserving (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index (excludedHeight (1 : Fin 4)) 1
    (excluded_simple_zero (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
      (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) 1) K
  apply le_antisymm _ bot_le
  exact (inf_le_inf hC hR).trans (le_of_eq (strict_inf_preserving
    (weight (CartanMatrix.D 4) (CartanMatrix.D_transpose 4) D4_positive_definite
      Base (excludedHeight (1 : Fin 4)))))

theorem longComplement_twist_le (K : Type) [Field K] (σ : K ≃+* K) :
    (longComplement K).map (unitTwist K σ).toMonoidHom ≤ longComplement K := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply (Subgroup.closure_le _).mpr
  rintro x (⟨⟨⟨j, hj⟩, t⟩, rfl⟩ | ⟨⟨⟨j, hj⟩, t⟩, rfl⟩)
  · have hj' : (1 : Fin 4) ≠ trialityPermutation j := by
      intro he
      apply hj
      apply trialityPermutation.injective
      exact he
    change unitTwist K σ (canonicalRoot rawData K false j t) ∈ longComplement K
    rw [unitTwist_raw_root]
    exact simple_mem_complement (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K 1 (trialityPermutation j) hj' (σ t)
  · have hj' : (1 : Fin 4) ≠ trialityPermutation j := by
      intro he
      apply hj
      apply trialityPermutation.injective
      exact he
    change unitTwist K σ (canonicalWeyl rawData K 1 * canonicalRoot rawData K false j t *
      (canonicalWeyl rawData K 1)⁻¹) ∈ longComplement K
    rw [map_mul, map_mul, map_inv, unitTwist_weyl, unitTwist_raw_root]
    change canonicalWeyl rawData K 1 * canonicalRoot rawData K false (trialityPermutation j)
      (σ t) * (canonicalWeyl rawData K 1)⁻¹ ∈ longComplement K
    exact conjugate_mem_complement (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K 1 (trialityPermutation j) hj' (σ t)

theorem centralRootGroup_twist_le (K : Type) [Field K] (σ : K ≃+* K) :
    (centralRootGroup K).map (unitTwist K σ).toMonoidHom ≤ centralRootGroup K := by
  apply Subgroup.map_le_iff_le_comap.mpr
  rintro x ⟨t, rfl⟩
  change unitTwist K σ (canonicalRoot rawData K false 1 t) ∈ centralRootGroup K
  rw [unitTwist_raw_root]
  change canonicalRoot rawData K false 1 (σ t) ∈ centralRootGroup K
  exact canonicalRoot_mem_subgroup rawData K false 1 (σ t)

theorem central_root_parameter_injective (K : Type) [Field K] :
    Function.Injective (canonicalRoot rawData K false (1 : Fin 4)) := by
  intro a b hab
  have he : positiveRoot (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
      (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
      K 1 a = positiveRoot (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
      (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
      K 1 b := Subtype.ext hab
  have hh := congrArg (leadingHom (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K) he
  rw [leadingHom_positiveRoot, leadingHom_positiveRoot] at hh
  have hentry := congrArg (fun c : Multiplicative (Fin 4 → K) => c.toAdd 1) hh
  simpa only [Pi.single_apply, if_true] using hentry

theorem exists_fixed_positive_long_factor (K : Type) [Field K] (σ : K ≃+* K)
    (u : (Matrix GeckIndex GeckIndex K)ˣ) (hu : u ∈ Positive K)
    (hfix : unitTwist K σ u = u) :
    ∃ c ∈ longComplement K, ∃ t : K,
      unitTwist K σ c = c ∧ σ t = t ∧ u = c * canonicalRoot rawData K false 1 t := by
  obtain ⟨c, hc, t, he⟩ := positive_factor (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index K 1 u hu
  change u = c * canonicalRoot rawData K false 1 t at he
  let o := canonicalRoot rawData K false 1 t
  have ho : o ∈ centralRootGroup K := canonicalRoot_mem_subgroup rawData K false 1 t
  have hc' : unitTwist K σ c ∈ longComplement K := longComplement_twist_le K σ ⟨c, hc, rfl⟩
  have ho' : unitTwist K σ o ∈ centralRootGroup K := centralRootGroup_twist_le K σ ⟨o, ho, rfl⟩
  have he' : unitTwist K σ c * unitTwist K σ o = c * o := by
    rw [← map_mul]
    change unitTwist K σ (c * canonicalRoot rawData K false 1 t) =
      c * canonicalRoot rawData K false 1 t
    rw [← he, hfix]
  have hinj : Function.Injective
      (fun z : longComplement K × centralRootGroup K => z.1.val * z.2.val) :=
    Subgroup.mul_injective_of_disjoint
      (disjoint_iff.mpr (longComplement_inf_centralRoot K))
  have hpair : ((⟨unitTwist K σ c, hc'⟩, ⟨unitTwist K σ o, ho'⟩) :
      longComplement K × centralRootGroup K) = (⟨c, hc⟩, ⟨o, ho⟩) := hinj he'
  have hcfix := congrArg (fun z : longComplement K × centralRootGroup K => z.1.val) hpair
  have hofix := congrArg (fun z : longComplement K × centralRootGroup K => z.2.val) hpair
  have ht : σ t = t := by
    apply central_root_parameter_injective K
    change unitTwist K σ (canonicalRoot rawData K false 1 t) =
      canonicalRoot rawData K false 1 t at hofix
    rw [unitTwist_raw_root] at hofix
    exact hofix
  exact ⟨c, hc, t, hcfix, ht, he⟩

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedLongComplementFactor
