import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMatrixTwist
import SymmetricSubgroupAsymptotics.CFSGTrialityD4PositiveRootIndex
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateFinitePositiveNormalForm
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositivePGroup

/-! Reuse of the checked actual positive normal form for D4 triality.
Source-Cartan transport changes no natural root unit. Consequently the
matrix twist acts on that SAME U, whose cardinality and p-group property
are inherited from the proved coordinate-group theorems. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckPositiveTwist
open CFSGNormTwoRootPairing CFSGTrialityD4NormTwo
open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckMatrixTwist
open CFSGSerreQuadraticMatrix CFSGNormTwoGeckPositivePGroup

theorem transported_root_eq (K : Type) [CommRing K] (neg : Bool) (i : Fin 4) (t : K) :
    canonicalRoot data K neg i t = canonicalRoot rawData K neg i t := by
  apply Units.ext
  simp only [canonicalRoot_val, data, fieldRoot, fieldSecond,
    transportSource_integerRoot, transportSource_integerSecond]

theorem simpleUpper_eq_positive (K : Type) [Field K] :
    simpleUpper K = rootGroup (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K false := by
  unfold simpleUpper rootGroup
  congr 1
  ext u
  constructor
  · rintro ⟨i, t, rfl⟩
    exact ⟨(i, t), (transported_root_eq K false i t).symm⟩
  · rintro ⟨⟨i, t⟩, rfl⟩
    exact ⟨i, t, (transported_root_eq K false i t).symm⟩

abbrev Positive (K : Type) [Field K] :=
  rootGroup (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index K false

theorem positive_twist_map (K : Type) [Field K] (σ : K ≃+* K) :
    (Positive K).map (unitTwist K σ).toMonoidHom = Positive K := by
  have h := unitTwist_upper K σ
  rw [simpleUpper_eq_positive K] at h
  exact h

def positiveTwist (K : Type) [Field K] (σ : K ≃+* K) : MulAut (Positive K) :=
  ((unitTwist K σ).subgroupMap (Positive K)).trans
    (MulEquiv.subgroupCongr (positive_twist_map K σ))

theorem positiveTwist_val (K : Type) [Field K] (σ : K ≃+* K) (u : Positive K) :
    (positiveTwist K σ u).val = unitTwist K σ u.val := rfl

theorem positive_card (K : Type) [Field K] : Nat.card (Positive K) = Nat.card K ^ 12 := by
  have hc := CFSGNormTwoCoordinatePositiveCardinality.positive_card
    (CartanMatrix.D 4) (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K
  change Nat.card (Positive K) = Nat.card K ^
    Nat.card CFSGTrialityD4PositiveRootIndex.Positive at hc
  rw [CFSGTrialityD4PositiveRootIndex.positive_card] at hc
  exact hc

theorem positive_isPGroup (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    IsPGroup p (Positive K) :=
  CFSGNormTwoCoordinatePositivePGroup.rootGroup_isPGroup
    (CartanMatrix.D 4) (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) Index K p false

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckPositiveTwist
