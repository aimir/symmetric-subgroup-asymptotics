import SymmetricSubgroupAsymptotics.CFSGTrialityGeckWordRootIndex

/-! Additive group equivalences for the ACTUAL word-parametrized root
lines. Their group law is derived from canonicalRoot_add and conjugation;
the already-proved root-line bijections give the inverse maps. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckSectionAdditiveParameters
open CFSGNormTwoRootPairing CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckFixedRootSections CFSGTrialityGeckSectionHeightMembership
open CFSGTrialityGeckSectionParameterRanges CFSGTrialityGeckSectionRootLabels
open CFSGTrialityGeckWordRootIndex CFSGTrialityD4PositiveRootOrbits
open CFSGSerreQuadraticMatrix CFSGNormTwoCoordinateSelectedRootAdditive
open CFSGNormTwoCoordinateAllRootParameters CFSGNormTwoCoordinatePositiveRootCardinality

private theorem conjugated_root_add (K : Type) [CommRing K]
    (u : (Matrix GeckIndex GeckIndex K)ˣ) (j : Fin 4) (a b : K) :
    (u * canonicalRoot rawData K false j a * u⁻¹) *
      (u * canonicalRoot rawData K false j b * u⁻¹) =
        u * canonicalRoot rawData K false j (a + b) * u⁻¹ := by
  calc
    _ = u * (canonicalRoot rawData K false j a * canonicalRoot rawData K false j b) * u⁻¹ := by group
    _ = _ := by rw [canonicalRoot_add]

def shortParameterHom (K : Type) [Field K] (s k : Fin 3) :
    Multiplicative K →* RootLine K (shortLabel s k) where
  toFun a := shortParameter K s k a.toAdd
  map_one' := by
    apply Subtype.ext
    change shortFactor K s k 0 = 1
    simp only [shortFactor, canonicalRoot_zero, mul_one, mul_inv_cancel]
  map_mul' a b := by
    apply Subtype.ext
    change shortFactor K s k (a.toAdd + b.toAdd) =
      shortFactor K s k a.toAdd * shortFactor K s k b.toAdd
    exact (conjugated_root_add K (shortTransport K s)
      (CFSGTrialityFixedWeylWords.outerNode k) a.toAdd b.toAdd).symm

def longParameterHom (K : Type) [Field K] (s : Fin 3) :
    Multiplicative K →* RootLine K (longRoot s) where
  toFun a := longParameter K s a.toAdd
  map_one' := by
    apply Subtype.ext
    change longSection K s false 0 = 1
    simp only [longSection, canonicalRoot_zero, mul_one, mul_inv_cancel]
  map_mul' a b := by
    apply Subtype.ext
    change longSection K s false (a.toAdd + b.toAdd) =
      longSection K s false a.toAdd * longSection K s false b.toAdd
    exact (conjugated_root_add K (longTransport K s) 1 a.toAdd b.toAdd).symm

def shortParameterMulEquiv (K : Type) [Field K] [Finite K] (s k : Fin 3) :
    Multiplicative K ≃* RootLine K (shortLabel s k) :=
  MulEquiv.ofBijective (shortParameterHom K s k)
    ((shortParameter_bijective K s k).comp Multiplicative.toAdd.bijective)

def longParameterMulEquiv (K : Type) [Field K] [Finite K] (s : Fin 3) :
    Multiplicative K ≃* RootLine K (longRoot s) :=
  MulEquiv.ofBijective (longParameterHom K s)
    ((longParameter_bijective K s).comp Multiplicative.toAdd.bijective)

def wordParameterMulEquiv (K : Type) [Field K] [Finite K] :
    (a : CFSGTrialityD4PositiveRootIndex.OrbitIndex) →
      Multiplicative K ≃* RootLine K (wordPositiveRoot a).val
  | Sum.inl s => longParameterMulEquiv K s
  | Sum.inr (s,k) => shortParameterMulEquiv K s k

def selectedParameterMulEquiv (K : Type) [Field K] (k : Roots (CartanMatrix.D 4)) :
    Multiplicative K ≃* RootLine K k :=
  (MonoidHom.ofInjective (selected_rootHom_injective (CartanMatrix.D 4)
    (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4) D4_positive_definite
    (CartanMatrix.D_off_diag_nonpos 4) K k)).trans
    (MulEquiv.subgroupCongr (selectedRootHom_range (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
      (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K k))

def parameterReparam (K : Type) [Field K] [Finite K]
    (a : CFSGTrialityD4PositiveRootIndex.OrbitIndex) : MulAut (Multiplicative K) :=
  (wordParameterMulEquiv K a).trans (selectedParameterMulEquiv K (wordPositiveRoot a).val).symm

theorem parameterReparam_spec (K : Type) [Field K] [Finite K]
    (a : CFSGTrialityD4PositiveRootIndex.OrbitIndex) (t : Multiplicative K) :
    selectedRootHom (CartanMatrix.D 4) (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K (wordPositiveRoot a).val
      (parameterReparam K a t) = (wordParameterMulEquiv K a t).val := by
  change (selectedParameterMulEquiv K (wordPositiveRoot a).val (parameterReparam K a t)).val = _
  exact congrArg Subtype.val
    ((selectedParameterMulEquiv K (wordPositiveRoot a).val).apply_symm_apply
      (wordParameterMulEquiv K a t))

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckSectionAdditiveParameters
