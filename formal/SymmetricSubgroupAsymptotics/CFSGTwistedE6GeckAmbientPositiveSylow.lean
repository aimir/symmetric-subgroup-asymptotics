import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckPositiveActionInjective
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveSylow
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNormalizerSoluble
import SymmetricSubgroupAsymptotics.CFSGExceptionalNormalizerWordIdentity

/-! Typed literal E6 ambient upper Sylow and soluble-normalizer data,
reusing the checked integral E6 normalizing-word identity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckAmbientPositiveSylow
open CFSGTwistedE6GeckPositiveActionInjective CFSGTwistedE6GeckSourceAction
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6GeckDiagramCovariance
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoCoordinatePositiveSylow CFSGExceptionalNormalizerWordIdentity
open CFSGSignedCartanReflections CFSGNormTwoCoordinateNormalizerSoluble

theorem positive_le_matrixGroup (K : Type) [Field K] : Positive K≤MatrixGroup K := by
  intro u hu
  exact (positiveInclusion K ⟨u,hu⟩).property

abbrev AmbientPositive (K : Type) [Field K] := (Positive K).subgroupOf (MatrixGroup K)

def ambientPositiveSylow (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] : Sylow p (MatrixGroup K) :=
  canonicalPositiveSylow CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K E6Signs E6_signs_square
    E6_signs_cartan (E6_normalizer_word_identity K) p

theorem ambientPositiveSylow_coe (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    (ambientPositiveSylow K p : Subgroup (MatrixGroup K))=AmbientPositive K := rfl

theorem ambient_normalizer_map_le (K : Type) [Field K] :
    (Subgroup.normalizer (AmbientPositive K : Set (MatrixGroup K))).map (MatrixGroup K).subtype≤
      Subgroup.normalizer (Positive K : Set (Matrix GeckIndex GeckIndex K)ˣ)⊓MatrixGroup K := by
  have hm : (AmbientPositive K).map (MatrixGroup K).subtype=Positive K := by
    rw [Subgroup.subgroupOf_map_subtype,inf_of_le_left (positive_le_matrixGroup K)]
  intro g hg
  have hn := (AmbientPositive K).le_normalizer_map (MatrixGroup K).subtype hg
  rw [hm] at hn
  refine ⟨hn,?_⟩
  obtain ⟨x,_,rfl⟩ := hg
  exact x.property

theorem ambient_positive_normalizer_soluble (K : Type) [Field K] :
    IsSolvable (Subgroup.normalizer (AmbientPositive K : Set (MatrixGroup K))) := by
  letI : IsSolvable (CFSGExceptionalDiagramAutomorphisms.diagramGroup CartanMatrix.E₆) :=
    CFSGExceptionalDiagramAutomorphisms.E6_diagram_soluble
  let N : Subgroup (Matrix GeckIndex GeckIndex K)ˣ :=
    Subgroup.normalizer (Positive K : Set (Matrix GeckIndex GeckIndex K)ˣ)⊓MatrixGroup K
  letI : IsSolvable N := normalizer_inter_model_soluble CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos
    K E6Signs E6_signs_square E6_signs_cartan
  let NH := Subgroup.normalizer (AmbientPositive K : Set (MatrixGroup K))
  let f : NH→*N :=
    { toFun := fun x=>⟨x.val.val,ambient_normalizer_map_le K ⟨x.val,x.property,rfl⟩⟩
      map_one' := rfl
      map_mul' := fun _ _=>rfl }
  apply solvable_of_solvable_injective (f:=f)
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : N=>z.val) h

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckAmbientPositiveSylow
