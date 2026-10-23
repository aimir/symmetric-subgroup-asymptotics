import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSectionHeightMembership
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateAllRootParameters

/-! The literal word parameters used by the fixed sections exhaust
their ACTUAL root lines. Over finite fields they are bijections, by
the proved root-line cardinality, with no recognition premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckSectionParameterRanges
open CFSGNormTwoRootPairing CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckFixedRootSections CFSGTrialityGeckSectionRootLabels
open CFSGTrialityGeckSectionHeightMembership CFSGNormTwoCoordinateRootWeylAction
open CFSGNormTwoCoordinateCanonicalSimpleRootLine CFSGNormTwoCoordinateAllRootParameters
open CFSGTrialityD4PositiveRootOrbits CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord

private theorem word_parameter_surjective (K : Type) [Field K] (w : List (Fin 4))
    (j : Fin 4) (k : Roots (CartanMatrix.D 4))
    (hw : CFSGTrialityD4RelativeRootWords.rootWord w (Index j) = k)
    (x : (Matrix GeckIndex GeckIndex K)ˣ) (hx : x ∈ RootLine K k) :
    ∃ t : K, canonicalWord rawData K w * canonicalRoot rawData K false j t *
      (canonicalWord rawData K w)⁻¹ = x := by
  have he := rootSubgroup_map_word (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
    K w (Index j)
  change (RootLine K (Index j)).map (MulAut.conj (canonicalWord rawData K w)).toMonoidHom =
    RootLine K (CFSGTrialityD4RelativeRootWords.rootWord w (Index j)) at he
  rw [hw] at he
  rw [← he] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have hs := rootSubgroup_simple_eq_canonical (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K j
  change RootLine K (Index j) = canonicalRootSubgroup rawData K false j at hs
  rw [hs] at hy
  obtain ⟨t, rfl⟩ := hy
  exact ⟨t, hyx⟩

def shortParameter (K : Type) [Field K] (s k : Fin 3) (t : K) : RootLine K (shortLabel s k) :=
  ⟨shortFactor K s k t, shortFactor_mem_root K s k t⟩

def longParameter (K : Type) [Field K] (s : Fin 3) (t : K) : RootLine K (longRoot s) :=
  ⟨longSection K s false t, longSection_mem_root K s t⟩

theorem shortParameter_surjective (K : Type) [Field K] (s k : Fin 3) :
    Function.Surjective (shortParameter K s k) := by
  intro x
  have hw : CFSGTrialityD4RelativeRootWords.rootWord (shortWord s)
      (Index (CFSGTrialityFixedWeylWords.outerNode k)) = shortLabel s k := by
    rw [← short_seed_index, short_word_label]
  obtain ⟨t, ht⟩ := word_parameter_surjective K (shortWord s)
    (CFSGTrialityFixedWeylWords.outerNode k) (shortLabel s k) hw x.val x.property
  refine ⟨t, Subtype.ext ?_⟩
  change shortFactor K s k t = x.val
  unfold shortFactor
  rw [shortTransport_word]
  exact ht

theorem longParameter_surjective (K : Type) [Field K] (s : Fin 3) :
    Function.Surjective (longParameter K s) := by
  intro x
  have hw : CFSGTrialityD4RelativeRootWords.rootWord (longWord s) (Index 1) = longRoot s := by
    rw [← long_seed_index, long_word_label]
  obtain ⟨t, ht⟩ := word_parameter_surjective K (longWord s) 1 (longRoot s) hw x.val x.property
  refine ⟨t, Subtype.ext ?_⟩
  change longSection K s false t = x.val
  unfold longSection
  rw [longTransport_word]
  exact ht

theorem shortParameter_bijective (K : Type) [Field K] [Finite K] (s k : Fin 3) :
    Function.Bijective (shortParameter K s k) := by
  apply (Nat.bijective_iff_surjective_and_card _).mpr
  refine ⟨shortParameter_surjective K s k, ?_⟩
  exact (rootSubgroup_card (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
    K (shortLabel s k)).symm

theorem longParameter_bijective (K : Type) [Field K] [Finite K] (s : Fin 3) :
    Function.Bijective (longParameter K s) := by
  apply (Nat.bijective_iff_surjective_and_card _).mpr
  refine ⟨longParameter_surjective K s, ?_⟩
  exact (rootSubgroup_card (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
    K (longRoot s)).symm

def shortParameterEquiv (K : Type) [Field K] [Finite K] (s k : Fin 3) :
    K ≃ RootLine K (shortLabel s k) :=
  Equiv.ofBijective _ (shortParameter_bijective K s k)

def longParameterEquiv (K : Type) [Field K] [Finite K] (s : Fin 3) :
    K ≃ RootLine K (longRoot s) :=
  Equiv.ofBijective _ (longParameter_bijective K s)

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckSectionParameterRanges
