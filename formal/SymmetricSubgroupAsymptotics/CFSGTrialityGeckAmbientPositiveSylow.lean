import SymmetricSubgroupAsymptotics.CFSGD4WeylDiscriminant
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWordDiagramAction
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLatticeWord
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateGoodSylow
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSourceWordAction

/-! The literal positive D4 matrix subgroup is an ambient Sylow and has
soluble ambient normalizer. The mod-two lattice obstruction supplies the
actual normalizing-word identity, including over fields of characteristic
two; no classical-group recognition or order formula is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckAmbientPositiveSylow
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckSourceWordAction CFSGTrialityGeckPositiveTwist
open CFSGNormTwoCoordinateWordDiagramAction CFSGNormTwoCoordinateLatticeWord
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylLatticeLinear
open CFSGCartanDiagramLinearAction CFSGNormTwoCoordinateNormalizerDiagonalFactor
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoCoordinateHeight
open CFSGNormTwoGeckHeightSupport CFSGNormTwoGeckBorelPowerElements
open CFSGSerreQuadraticMatrix

def cartanSign : Fin 4 → ℤ := ![1,-1,1,1]

theorem cartanSign_square : ∀ i, cartanSign i * cartanSign i = 1 := by decide

theorem cartanSign_pairing : ∀ i j,
    cartanSign i * |CartanMatrix.D 4 i j| = CartanMatrix.D 4 j i * cartanSign j := by decide

theorem normalizer_word_identity (K : Type) [Field K] (w : List (Fin 4))
    (hn : wordUnit (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index K w ∈
        Subgroup.normalizer (Positive K : Set (Matrix GeckIndex GeckIndex K)ˣ)) :
    wordLinear (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index w = 1 := by
  obtain ⟨σ, he, hA⟩ := normalizer_word_action (CartanMatrix.D 4)
    (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4) D4_positive_definite
    (CartanMatrix.D_off_diag_nonpos 4) K w hn
  change wordLinear (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index w = permutationLinear σ at he
  have hσ : σ = 1 := CFSGD4WeylDiscriminant.diagram_eq_one_of_word_action w σ hA (by
    intro x
    have hh := LinearMap.congr_fun (latticeWord_linear (CartanMatrix.D 4)
      (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4) D4_positive_definite
      (CartanMatrix.D_off_diag_nonpos 4) w) x
    change CFSGSignedCartanReflections.latticeWord (CartanMatrix.D 4) w *ᵥ x =
      wordLinear (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
        D4_positive_definite Base Index w x at hh
    rw [he] at hh
    exact hh)
  rw [he, hσ, map_one]

theorem positive_le_matrixGroup (K : Type) [Field K] : Positive K ≤ MatrixGroup K := by
  change CFSGNormTwoGeckPositivePGroup.rootGroup (CartanMatrix.D 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite Base Index K false ≤
      canonicalElementaryGroup (CFSGNormTwoGeckIntegralRealization.realizationData
        (CartanMatrix.D 4) (CartanMatrix.D_transpose 4) D4_positive_definite Base Index) K
  rw [← positive_sup_negative (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index K]
  exact le_sup_left

abbrev AmbientPositive (K : Type) [Field K] := (Positive K).subgroupOf (MatrixGroup K)

theorem ambientPositive_isPGroup (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] : IsPGroup p (AmbientPositive K) :=
  (CFSGNormTwoGeckPositivePGroup.positive_isPGroup (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index coordinateHeight
    (CFSGNormTwoCoordinateHeight.simple_height (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
      (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)) K p).of_injective
    (Subgroup.subgroupOfEquivOfLe (positive_le_matrixGroup K)).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe (positive_le_matrixGroup K)).injective

theorem ambient_normalizer_map_le (K : Type) [Field K] :
    (Subgroup.normalizer (AmbientPositive K : Set (MatrixGroup K))).map (MatrixGroup K).subtype ≤
      Subgroup.normalizer (Positive K : Set _) ⊓ MatrixGroup K := by
  have hm : (AmbientPositive K).map (MatrixGroup K).subtype = Positive K := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left (positive_le_matrixGroup K)]
  intro g hg
  have hn := (AmbientPositive K).le_normalizer_map (MatrixGroup K).subtype hg
  rw [hm] at hn
  refine ⟨hn, ?_⟩
  obtain ⟨x, _, rfl⟩ := hg
  exact x.property

def ambientPositiveSylow (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] : Sylow p (MatrixGroup K) := by
  apply CFSGSylowNormalizerMaximality.sylowOfNormalizer (AmbientPositive K)
    (ambientPositive_isPGroup K p)
  intro P hP hPN
  have hmap := (Subgroup.map_mono hPN).trans (ambient_normalizer_map_le K)
  have hle := pSubgroup_normalizer_le_positive (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
    K cartanSign cartanSign_square cartanSign_pairing (normalizer_word_identity K) p
    (P.map (MatrixGroup K).subtype) (hP.map (MatrixGroup K).subtype)
    (hmap.trans inf_le_right) (hmap.trans inf_le_left)
  intro x hx
  exact hle ⟨x, hx, rfl⟩

theorem ambientPositiveSylow_subgroup (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    (ambientPositiveSylow K p : Subgroup (MatrixGroup K)) = AmbientPositive K := rfl

theorem ambient_positive_normalizer_soluble (K : Type) [Field K] :
    IsSolvable (Subgroup.normalizer (AmbientPositive K : Set (MatrixGroup K))) := by
  let N : Subgroup (Matrix GeckIndex GeckIndex K)ˣ :=
    Subgroup.normalizer (Positive K : Set (Matrix GeckIndex GeckIndex K)ˣ) ⊓ MatrixGroup K
  obtain ⟨e, he⟩ := CFSGFiniteWeightFlag.exists_flag
    (weight (CartanMatrix.D 4) (CartanMatrix.D_transpose 4) D4_positive_definite Base coordinateHeight)
  letI : IsSolvable N := CFSGDiagonalUnipotentExtension.subgroup_soluble e N (Positive K)
    (positive_le_unipotent (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite Base Index coordinateHeight
      (CFSGNormTwoCoordinateHeight.simple_height (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
        (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)) K e he)
    (fun g hg => normalizer_diagonal_factor (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
      (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
      K cartanSign cartanSign_square cartanSign_pairing (normalizer_word_identity K) g hg.2 hg.1)
  let NH := Subgroup.normalizer (AmbientPositive K : Set (MatrixGroup K))
  let f : NH →* N :=
    { toFun := fun x => ⟨x.val.val, ambient_normalizer_map_le K ⟨x.val, x.property, rfl⟩⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  apply solvable_of_solvable_injective (f := f)
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : N => z.val) h

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckAmbientPositiveSylow
