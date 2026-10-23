import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSectionAdditiveParameters
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckHeightQuotientTwist
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHeightLayerCoordinates

/-! Genuine independent coordinates on each actual height image, using
the literal word parameters of the fixed triality sections. The group
equivalence is a proved reparameterization of the checked height chart. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckWordHeightCoordinates
open CFSGNormTwoRootPairing CFSGTrialityD4NormTwo CFSGTrialityGeckPositiveTwist
open CFSGTrialityGeckWordRootIndex CFSGTrialityGeckSectionAdditiveParameters
open CFSGTrialityGeckHeightQuotientTwist CFSGTrialityGeckSectionHeightMembership
open CFSGNormTwoCoordinateRootHeightQuotient CFSGNormTwoCoordinateRootHeightFiltration
open CFSGNormTwoCoordinatePositiveRootGenerators CFSGNormTwoCoordinateExactHeightLayer
open CFSGNormTwoCoordinateHeightLayerCoordinates

local instance wordHeightTailNormal (K : Type) [Field K] (h : ℤ) :
    (TailInPositive K h).Normal :=
  heightTail_normal_in_positive (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K h

def coordinateReparam (K : Type) [Field K] [Finite K] (h : ℤ) :
    (WordHeightIndex h → Multiplicative K) ≃*
      (ExactHeightRoot (CartanMatrix.D 4) h → Multiplicative K) where
  toFun c k := parameterReparam K ((wordHeightEquiv h).symm k).val
    (c ((wordHeightEquiv h).symm k))
  invFun d j := (parameterReparam K j.val).symm (d (wordHeightEquiv h j))
  left_inv c := by
    funext j
    simp only [Equiv.symm_apply_apply, MulEquiv.symm_apply_apply]
  right_inv d := by
    funext k
    simp only [MulEquiv.apply_symm_apply, Equiv.apply_symm_apply]
  map_mul' c d := by
    funext k
    exact map_mul (parameterReparam K ((wordHeightEquiv h).symm k).val) _ _

abbrev HeightImage (K : Type) [Field K] (h : ℤ) :=
  (TailInPositive K h).map (QuotientGroup.mk' (TailInPositive K (h + 1)))

def wordHeightLayerEquiv (K : Type) [Field K] [Finite K] (h : ℤ) (hh : 0 < h) :
    (WordHeightIndex h → Multiplicative K) ≃* HeightImage K h :=
  (coordinateReparam K h).trans
    (heightLayerEquiv (CartanMatrix.D 4) (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4)
      D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K h hh)

def wordPositiveParameterHom (K : Type) [Field K] [Finite K]
    (a : CFSGTrialityD4PositiveRootIndex.OrbitIndex) : Multiplicative K →* Positive K :=
  (((RootLine K (wordPositiveRoot a).val).subtype).comp
    (wordParameterMulEquiv K a).toMonoidHom).codRestrict (Positive K) (fun t =>
      positive_root_subgroup_le (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
        (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
        K (wordPositiveRoot a).val (wordPositiveRoot a).property
        (wordParameterMulEquiv K a t).property)

theorem coordinateReparam_mulSingle (K : Type) [Field K] [Finite K] (h : ℤ)
    (j : WordHeightIndex h) (t : Multiplicative K) :
    coordinateReparam K h (Pi.mulSingle j t) =
      Pi.mulSingle (wordHeightEquiv h j) (parameterReparam K j.val t) := by
  funext k
  change parameterReparam K ((wordHeightEquiv h).symm k).val
    ((Pi.mulSingle j t : WordHeightIndex h → Multiplicative K) ((wordHeightEquiv h).symm k)) =
      (Pi.mulSingle (wordHeightEquiv h j) (parameterReparam K j.val t) :
        ExactHeightRoot (CartanMatrix.D 4) h → Multiplicative K) k
  by_cases hk : k = wordHeightEquiv h j
  · subst k
    rw [Equiv.symm_apply_apply]
    simp [Pi.mulSingle_apply]
  · have hn : (wordHeightEquiv h).symm k ≠ j := by
      intro he
      apply hk
      calc
        k = wordHeightEquiv h ((wordHeightEquiv h).symm k) :=
          ((wordHeightEquiv h).apply_symm_apply k).symm
        _ = wordHeightEquiv h j := congrArg (wordHeightEquiv h) he
    simp [Pi.mulSingle_apply, hk, hn, Ne.symm hk, Ne.symm hn]

theorem wordHeightLayerEquiv_mulSingle (K : Type) [Field K] [Finite K]
    (h : ℤ) (hh : 0 < h) (j : WordHeightIndex h) (t : Multiplicative K) :
    (wordHeightLayerEquiv K h hh (Pi.mulSingle j t)).val =
      QuotientGroup.mk' (TailInPositive K (h + 1)) (wordPositiveParameterHom K j.val t) := by
  change exactHeightProductHom (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
    K h hh (coordinateReparam K h (Pi.mulSingle j t)) = _
  rw [coordinateReparam_mulSingle]
  simp only [exactHeightProductHom, MonoidHom.noncommPiCoprod_mulSingle]
  change QuotientGroup.mk' (TailInPositive K (h + 1))
    (positiveRootParameterHom (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
      (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
      K (wordPositiveRoot j.val).val (wordPositiveRoot j.val).property
      (parameterReparam K j.val t)) = _
  apply congrArg (QuotientGroup.mk' (TailInPositive K (h + 1)))
  apply Subtype.ext
  exact parameterReparam_spec K j.val t

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckWordHeightCoordinates
