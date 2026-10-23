import SymmetricSubgroupAsymptotics.CFSGGTwoHigherPositiveCommutation
import SymmetricSubgroupAsymptotics.CFSGGTwoRootParameters
import SymmetricSubgroupAsymptotics.CFSGGTwoPositiveSimpleCollecting
import SymmetricSubgroupAsymptotics.CFSGGTwoPositiveSixWord

/-! Collecting inside the SAME original G2 Model. All native identities are
transported by the checked unconditional Model equivalence. In characteristic
three the four higher axes are an actual additive four-coordinate subgroup;
no fixed-point lifting or recognition of a full positive subgroup is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoOriginalPositiveCollecting
open CFSG.Models.Chevalley CFSGGTwoSerreMatrices CFSGGTwoPositiveDirections
open CFSGGTwoRootParameters CFSGGTwoOriginalNaturalEquivalence
open CFSGGTwoOriginalPositiveRootWords CFSGGTwoHigherPositiveCommutation

variable (K : Type) [Field K]

theorem positiveRoot_add (j : Fin 6) (a b : K) :
    positiveRoot K j a * positiveRoot K j b = positiveRoot K j (a+b) := by
  unfold positiveRoot
  rw [show directionWord K j * rootTransvection K false (rootNode j) a *
      (directionWord K j)⁻¹ *
      (directionWord K j * rootTransvection K false (rootNode j) b *
        (directionWord K j)⁻¹) =
      directionWord K j *
        (rootTransvection K false (rootNode j) a * rootTransvection K false (rootNode j) b) *
          (directionWord K j)⁻¹ by group]
  rw [rootTransvection_add]

theorem positiveModel_add (j : Fin 6) (a b : K) :
    positiveModel K j a * positiveModel K j b = positiveModel K j (a+b) := by
  apply (modelEquivNatural K).injective
  apply Subtype.ext
  simpa only [map_mul, Subgroup.coe_mul, positiveModel_native] using positiveRoot_add K j a b

theorem positiveModel_zero (j : Fin 6) : positiveModel K j 0 = 1 := by
  have h := positiveModel_add K j 0 0
  simpa only [add_zero, mul_eq_left] using h

theorem simple_collecting (a b : K) :
    positiveModel K 1 b * positiveModel K 0 a =
      positiveModel K 0 a * positiveModel K 1 b *
        positiveModel K 2 (-a*b) * positiveModel K 3 (-a^2*b) *
          positiveModel K 4 (-a^3*b) * positiveModel K 5 (a^3*b^2) := by
  apply (modelEquivNatural K).injective
  apply Subtype.ext
  simpa only [map_mul, Subgroup.coe_mul, positiveModel_native] using
    CFSGGTwoPositiveSimpleCollecting.simple_collecting K a b

variable [CharP K 3]

theorem higher_commute (i j : Fin 4) (a b : K) :
    Commute (positiveModel K (higherIndex i) a) (positiveModel K (higherIndex j) b) := by
  change _ * _ = _ * _
  apply (modelEquivNatural K).injective
  apply Subtype.ext
  simpa only [map_mul, Subgroup.coe_mul, positiveModel_native] using
    (positive_higher_commute K i j a b).eq

/-- Four higher coordinates in their checked native ordering. -/
def higherWord (x : Fin 4 → K) : Model CartanMatrix.G₂ K :=
  positiveModel K 2 (x 0) * positiveModel K 3 (x 1) *
    positiveModel K 4 (x 2) * positiveModel K 5 (x 3)

private theorem merge_four {G : Type*} [Monoid G] (x y : Fin 4 → G)
    (h : ∀ i j, Commute (x i) (y j)) :
    x 0*x 1*x 2*x 3*(y 0*y 1*y 2*y 3) =
      (x 0*y 0)*(x 1*y 1)*(x 2*y 2)*(x 3*y 3) := by
  have hmiddle : Commute (x 2*x 3) (y 0*y 1) :=
    ((h 2 0).mul_right (h 2 1)).mul_left ((h 3 0).mul_right (h 3 1))
  calc
    _ = (x 0*x 1)*(x 2*x 3)*((y 0*y 1)*(y 2*y 3)) := by simp only [mul_assoc]
    _ = (x 0*x 1)*(y 0*y 1)*((x 2*x 3)*(y 2*y 3)) :=
      hmiddle.mul_mul_mul_comm _ _
    _ = (x 0*y 0)*(x 1*y 1)*((x 2*y 2)*(x 3*y 3)) := by
      rw [(h 1 0).mul_mul_mul_comm, (h 3 2).mul_mul_mul_comm]
    _ = _ := by simp only [mul_assoc]

theorem higherWord_add (x y : Fin 4 → K) :
    higherWord K x * higherWord K y = higherWord K (x+y) := by
  have h := merge_four
    (fun i => positiveModel K (higherIndex i) (x i))
    (fun i => positiveModel K (higherIndex i) (y i))
    (fun i j => higher_commute K i j (x i) (y j))
  change higherWord K x * higherWord K y =
    (positiveModel K 2 (x 0)*positiveModel K 2 (y 0))*
      (positiveModel K 3 (x 1)*positiveModel K 3 (y 1))*
      (positiveModel K 4 (x 2)*positiveModel K 4 (y 2))*
      (positiveModel K 5 (x 3)*positiveModel K 5 (y 3)) at h
  rw [h]
  simp only [positiveModel_add]
  rfl

theorem higherWord_rotate (a b c d : K) :
    positiveModel K 4 a * positiveModel K 5 b *
      positiveModel K 2 c * positiveModel K 3 d = higherWord K ![c,d,a,b] := by
  have h : Commute (positiveModel K 4 a * positiveModel K 5 b)
      (positiveModel K 2 c * positiveModel K 3 d) :=
    ((higher_commute K 2 0 a c).mul_right (higher_commute K 2 1 a d)).mul_left
      ((higher_commute K 3 0 b c).mul_right (higher_commute K 3 1 b d))
  calc
    _ = (positiveModel K 4 a * positiveModel K 5 b)*
      (positiveModel K 2 c * positiveModel K 3 d) := by simp only [mul_assoc]
    _ = (positiveModel K 2 c * positiveModel K 3 d)*
      (positiveModel K 4 a * positiveModel K 5 b) := h.eq
    _ = _ := by simp only [higherWord, mul_assoc]; rfl

end SymmetricSubgroupAsymptotics.CFSGGTwoOriginalPositiveCollecting
