import SymmetricSubgroupAsymptotics.CFSGTrialityGeckActionPElementSeparation
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckGeneratedActionImage

/-! Actual positive and literal-opposition negative actions have trivial
intersection. Central-kernel separation of p-elements is used before
reading the matrix intersection; separate positive injectivity is not
mistaken for joint injectivity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckOppositeActionIntersection
open CFSGTrialityD4NormTwo CFSGTrialityGeckSourceWordAction CFSGTrialityGeckPositiveTwist
open CFSGTrialityGeckAmbientPositiveSylow CFSGTrialityGeckActionPElementSeparation
open CFSGTrialityGeckRelativeOpposition CFSGTrialityGeckGeneratedActionImage
open CFSGNormTwoGeckPositivePGroup CFSGNormTwoGeckOppositeIntersection
open CFSGNormTwoCoordinateHeight

variable (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]

include p in
theorem positive_opposite_action_eq_imp_one (u v : Positive K)
    (he : positiveAction K u =
      matrixAction K (matrixWord K oppositionWord) * positiveAction K v *
        (matrixAction K (matrixWord K oppositionWord))⁻¹) : u = 1 := by
  let up : AmbientPositive K := ⟨positiveInclusion K u,u.property⟩
  let vp : AmbientPositive K := ⟨positiveInclusion K v,v.property⟩
  let O := matrixWord K oppositionWord
  obtain ⟨a,ha⟩ := ambientPositive_isPGroup K p up
  obtain ⟨b,hb⟩ := ambientPositive_isPGroup K p vp
  have hx : ∃ a : ℕ,up.val ^ p ^ a = 1 := ⟨a,congrArg Subtype.val ha⟩
  have hy : ∃ b : ℕ,(O*vp.val*O⁻¹) ^ p ^ b = 1 := by
    refine ⟨b,?_⟩
    have hbp : vp.val ^ p ^ b = 1 := congrArg (fun z : AmbientPositive K => z.val) hb
    have hh := congrArg (MulAut.conj O) hbp
    simpa only [map_pow,map_one] using hh
  have hmap : matrixAction K up.val = matrixAction K (O*vp.val*O⁻¹) := by
    simpa only [map_mul,map_inv] using he
  have hm := matrixAction_eq_of_p_elements K p up.val (O*vp.val*O⁻¹) hx hy hmap
  have hn : (O*vp.val*O⁻¹).val ∈ rootGroup (CartanMatrix.D 4)
      (CartanMatrix.D_transpose 4) D4_positive_definite Base Index K true := by
    change O.val*v.val*O.val⁻¹ ∈ rootGroup (CartanMatrix.D 4)
      (CartanMatrix.D_transpose 4) D4_positive_definite Base Index K true
    dsimp only [O]
    rw [matrixOpposition_val]
    exact positive_image_le_negative K ⟨v.val,v.property,rfl⟩
  have hraw : u.val = (O*vp.val*O⁻¹).val :=
    congrArg (fun x : MatrixGroup K => x.val) hm
  rw [←hraw] at hn
  have hz : u.val ∈ Positive K ⊓ rootGroup (CartanMatrix.D 4)
      (CartanMatrix.D_transpose 4) D4_positive_definite Base Index K true := ⟨u.property,hn⟩
  rw [positive_inf_negative (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index coordinateHeight
    (simple_height (CartanMatrix.D 4) (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)) K,Subgroup.mem_bot] at hz
  exact Subtype.ext hz

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckOppositeActionIntersection
