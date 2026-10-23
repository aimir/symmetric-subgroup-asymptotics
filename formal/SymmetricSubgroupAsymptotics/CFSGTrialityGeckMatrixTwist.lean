import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRootAction
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCanonicalWeyl
import Mathlib.Algebra.Group.Units.Equiv

/-! A literal diagram--field automorphism of the natural Geck matrices.
Its simple-root formula is derived from the checked ORIGINAL D4 integral
coefficient covariance. Positive-root closure is preserved, with no
triality-invariant total ordering of the roots. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMatrixTwist
open CFSGTrialityGeckDiagramCovariance CFSGSerreQuadraticMatrix
open CFSGQuadraticRootReindex CFSGSerreDiagram
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) :=
  Classical.decEq _

theorem integer_root_triality (neg : Bool) (i : Fin 4) :
    Matrix.reindexAlgEquiv ℤ ℤ trialityIndex (integerRoot data neg i) =
      integerRoot data neg (trialityPermutation i) := by
  cases neg
  · exact integerGenerator_triality (.E i)
  · exact integerGenerator_triality (.F i)

theorem field_root_triality (K : Type) [CommRing K] (neg : Bool) (i : Fin 4) :
    Matrix.reindexAlgEquiv K K trialityIndex (fieldRoot data K neg i) =
      fieldRoot data K neg (trialityPermutation i) :=
  fieldRoot_reindex data trialityIndex trialityPermutation integer_root_triality K neg i

theorem field_second_triality (K : Type) [CommRing K] (neg : Bool) (i : Fin 4) :
    Matrix.reindexAlgEquiv K K trialityIndex (fieldSecond data K neg i) =
      fieldSecond data K neg (trialityPermutation i) :=
  fieldSecond_reindex data trialityIndex trialityPermutation integer_root_triality K neg i

def matrixTwist (K : Type) [CommRing K] (σ : K ≃+* K) :
    Matrix GeckIndex GeckIndex K ≃+* Matrix GeckIndex GeckIndex K :=
  σ.mapMatrix.trans (Matrix.reindexAlgEquiv K K trialityIndex).toRingEquiv

def unitTwist (K : Type) [CommRing K] (σ : K ≃+* K) :
    MulAut ((Matrix GeckIndex GeckIndex K)ˣ) :=
  Units.mapEquiv (matrixTwist K σ).toMulEquiv

theorem unitTwist_root (K : Type) [CommRing K] (σ : K ≃+* K)
    (neg : Bool) (i : Fin 4) (t : K) :
    unitTwist K σ (canonicalRoot data K neg i t) =
      canonicalRoot data K neg (trialityPermutation i) (σ t) := by
  apply Units.ext
  change Matrix.reindexAlgEquiv K K trialityIndex
    (σ.toRingHom.mapMatrix (canonicalRoot data K neg i t : Matrix GeckIndex GeckIndex K)) = _
  rw [map_canonicalRoot_val, canonicalRoot_val, canonicalRoot_val]
  simp only [map_add, map_one, map_smul, field_root_triality, field_second_triality]
  rfl

def simpleUpper (K : Type) [CommRing K] : Subgroup (Matrix GeckIndex GeckIndex K)ˣ :=
  Subgroup.closure {u | ∃ i : Fin 4, ∃ t : K, u = canonicalRoot data K false i t}

theorem unitTwist_upper_le (K : Type) [CommRing K] (σ : K ≃+* K) :
    (simpleUpper K).map (unitTwist K σ).toMonoidHom ≤ simpleUpper K := by
  apply (Subgroup.map_le_iff_le_comap).mpr
  apply (Subgroup.closure_le _).mpr
  rintro u ⟨i, t, rfl⟩
  change unitTwist K σ (canonicalRoot data K false i t) ∈ simpleUpper K
  rw [unitTwist_root]
  exact Subgroup.subset_closure ⟨trialityPermutation i, σ t, rfl⟩

theorem unitTwist_upper (K : Type) [CommRing K] (σ : K ≃+* K) :
    (simpleUpper K).map (unitTwist K σ).toMonoidHom = simpleUpper K := by
  apply le_antisymm (unitTwist_upper_le K σ)
  apply (Subgroup.closure_le _).mpr
  rintro u ⟨i, t, rfl⟩
  refine ⟨canonicalRoot data K false (trialityPermutation.symm i) (σ.symm t),
    Subgroup.subset_closure ⟨trialityPermutation.symm i, σ.symm t, rfl⟩, ?_⟩
  change unitTwist K σ
    (canonicalRoot data K false (trialityPermutation.symm i) (σ.symm t)) = _
  rw [unitTwist_root, Equiv.apply_symm_apply, RingEquiv.apply_symm_apply]

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMatrixTwist
