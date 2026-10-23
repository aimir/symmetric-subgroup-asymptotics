import SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortComplementFactor
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLeadingHom

/-! The three outer simple-root factors have genuine independent
parameters, read from actual simple leading entries. This chart is for
the literal matrix subgroup and works in every characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckOuterParameterChart
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckPositiveTwist CFSGTrialityGeckShortComplementFactor
open CFSGTrialityFixedWeylWords CFSGSerreQuadraticMatrix
open CFSGNormTwoCoordinateLeadingHom CFSGNormTwoCoordinateLeadingFactor

theorem outerProductHom_mulSingle (K : Type) [Field K] (i : Fin 3) (t : Multiplicative K) :
    outerProductHom K (Pi.mulSingle i t) = canonicalRoot rawData K false (outerNode i) t.toAdd :=
  MonoidHom.noncommPiCoprod_mulSingle (outerRootHom K) i t

def outerPositiveHom (K : Type) [Field K] : (Fin 3 → Multiplicative K) →* Positive K :=
  (outerProductHom K).codRestrict (Positive K) (fun a => outerGroup_le_positive K ⟨a, rfl⟩)

def outerLeadingHom (K : Type) [Field K] : Positive K →* (Fin 3 → Multiplicative K) where
  toFun u i := Multiplicative.ofAdd (leadingCoordinates (CartanMatrix.D 4)
    (CartanMatrix.D_diag 4) (CartanMatrix.D_transpose 4) D4_positive_definite
    (CartanMatrix.D_off_diag_nonpos 4) K u.val (outerNode i))
  map_one' := by
    funext i
    change leadingCoordinates (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
      (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K 1
      (outerNode i) = 0
    rw [leadingCoordinates_one]
    rfl
  map_mul' u v := by
    funext i
    change leadingCoordinates (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
      (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K
      (u.val * v.val) (outerNode i) =
        leadingCoordinates (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
          (CartanMatrix.D_transpose 4) D4_positive_definite
          (CartanMatrix.D_off_diag_nonpos 4) K u.val (outerNode i) +
        leadingCoordinates (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
          (CartanMatrix.D_transpose 4) D4_positive_definite
          (CartanMatrix.D_off_diag_nonpos 4) K v.val (outerNode i)
    exact congrFun (leadingCoordinates_mul (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
      (CartanMatrix.D_transpose 4) D4_positive_definite
      (CartanMatrix.D_off_diag_nonpos 4) K u v) (outerNode i)

theorem outer_leading_mulSingle (K : Type) [Field K] (i : Fin 3) (t : Multiplicative K) :
    outerLeadingHom K (outerPositiveHom K (Pi.mulSingle i t)) = Pi.mulSingle i t := by
  funext j
  change leadingCoordinates (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K
    (outerProductHom K (Pi.mulSingle i t)) (outerNode j) =
      ((Pi.mulSingle i t : Fin 3 → Multiplicative K) j).toAdd
  rw [outerProductHom_mulSingle]
  have hh := congrArg (fun c : Multiplicative (Fin 4 → K) => c.toAdd (outerNode j))
    (leadingHom_positiveRoot (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
      (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4)
      K (outerNode i) t.toAdd)
  change leadingCoordinates (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K
      (canonicalRoot rawData K false (outerNode i) t.toAdd) (outerNode j) =
        (Pi.single (outerNode i) t.toAdd : Fin 4 → K) (outerNode j) at hh
  rw [hh]
  by_cases hij : i = j
  · subst j
    simp
  · have hji : outerNode j ≠ outerNode i := fun h => hij (outerNode_injective h).symm
    simp [Ne.symm hij, hji]

theorem outer_leading_left_inverse (K : Type) [Field K] (a : Fin 3 → Multiplicative K) :
    outerLeadingHom K (outerPositiveHom K a) = a := by
  apply Pi.mulSingle_induction (fun b : Fin 3 → Multiplicative K =>
    outerLeadingHom K (outerPositiveHom K b) = b) a
  · simp only [map_one]
  · intro b c hb hc
    rw [map_mul, map_mul, hb, hc]
  · exact outer_leading_mulSingle K

theorem outerProductHom_injective (K : Type) [Field K] : Function.Injective (outerProductHom K) := by
  intro a b h
  have hp : outerPositiveHom K a = outerPositiveHom K b := Subtype.ext h
  have hh := congrArg (outerLeadingHom K) hp
  rw [outer_leading_left_inverse, outer_leading_left_inverse] at hh
  exact hh

theorem outerProductHom_explicit (K : Type) [Field K] (a : Fin 3 → Multiplicative K) :
    outerProductHom K a = canonicalRoot rawData K false 0 (a 0).toAdd *
      canonicalRoot rawData K false 2 (a 1).toAdd * canonicalRoot rawData K false 3 (a 2).toAdd := by
  have ha : a = Pi.mulSingle 0 (a 0) * Pi.mulSingle 1 (a 1) * Pi.mulSingle 2 (a 2) := by
    funext i
    fin_cases i <;> simp
  calc
    outerProductHom K a = outerProductHom K
      (Pi.mulSingle 0 (a 0) * Pi.mulSingle 1 (a 1) * Pi.mulSingle 2 (a 2)) := congrArg _ ha
    _ = _ := by rw [map_mul, map_mul, outerProductHom_mulSingle,
      outerProductHom_mulSingle, outerProductHom_mulSingle]; rfl

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckOuterParameterChart
