import SymmetricSubgroupAsymptotics.CFSGTwistedDNormalizedCommonNeighbours
import SymmetricSubgroupAsymptotics.CFSGTwistedDSingularDimensionBound
import SymmetricSubgroupAsymptotics.CFSGQuadraticWittThreeAxisBound
import SymmetricSubgroupAsymptotics.CFSGPolarCommonNeighbourUnique
import SymmetricSubgroupAsymptotics.CFSGTwoPlaneIntersectionCoordinates

/-! Actual disjoint fixed-field planes have at most (q+1)^2 common
adjacency neighbours. In original rank four the genuine nonsplit
Witt-three ceiling sharpens this to one, in every characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDDisjointCommonNeighbours
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDPlaneFamilyAction
open CFSGTwistedDPlaneAdjacencyActions CFSGTwistedDNormalizedCommonNeighbours
open CFSGTwistedDSingularDimensionBound CFSGTwistedA2FixedField
open CFSGOrthogonalDIndexQuadraticNeighborPlane CFSGTwoPlaneIntersectionCoordinates

local instance (n : ℕ) (q : CFSG.PrimePower) :
    Module.Finite (fixedField q) (fixedSpace n q) := Module.Finite.of_finite

theorem cross_of_adjacent (s : ℕ) (q : CFSG.PrimePower) (P R : SingularPlanes s q)
    (h : PlaneAdjacent s q P R) : ∀ p ∈ P.val, ∀ r ∈ R.val,
      (fixedQuadraticForm (s + 2) q).polarBilin p r = 0 := by
  intro p hp r hr
  exact polar_zero_of_singular (fixedQuadraticForm (s + 2) q) (P.val ⊔ R.val) h.2.2 p r
    ((show P.val ≤ P.val ⊔ R.val from le_sup_left) hp)
    ((show R.val ≤ P.val ⊔ R.val from le_sup_right) hr)

private theorem rank_four_cross_axis_le_one (q : CFSG.PrimePower)
    (P Q : SingularPlanes 0 q) (hd : Disjoint P.val Q.val) :
    Module.finrank (fixedField q)
      (P.val ⊓ (LinearMap.BilinForm.orthogonal (fixedQuadraticForm 2 q).polarBilin Q.val) :
        Submodule (fixedField q) (fixedSpace 2 q)) ≤ 1 :=
  CFSGQuadraticWittThreeAxisBound.cross_axis_finrank_le_one (fixedQuadraticForm 2 q)
    (fun S hs => original_rank_singular_finrank_le 0 q S hs) P.val Q.val
    P.property.1 Q.property.1 hd P.property.2 Q.property.2

private theorem rank_four_cross_axis_eq_one_of_common (q : CFSG.PrimePower)
    (P Q R : SingularPlanes 0 q) (hd : Disjoint P.val Q.val)
    (hPR : PlaneAdjacent 0 q P R) (hQR : PlaneAdjacent 0 q Q R) :
    Module.finrank (fixedField q)
      (P.val ⊓ (LinearMap.BilinForm.orthogonal (fixedQuadraticForm 2 q).polarBilin Q.val) :
        Submodule (fixedField q) (fixedSpace 2 q)) = 1 := by
  have hle : P.val ⊓ R.val ≤ P.val ⊓ (LinearMap.BilinForm.orthogonal (fixedQuadraticForm 2 q).polarBilin Q.val) := by
    intro x hx
    exact ⟨hx.1, fun y hy => cross_of_adjacent 0 q Q R hQR y hy x hx.2⟩
  have hlo := Submodule.finrank_mono hle
  rw [hPR.2.1] at hlo
  exact Nat.le_antisymm (rank_four_cross_axis_le_one q P Q hd) hlo

theorem rank_four_commonNeighbours_subsingleton (q : CFSG.PrimePower)
    (P Q : SingularPlanes 0 q) (hd : Disjoint P.val Q.val) :
    Subsingleton (CommonNeighbours 0 q P Q) := by
  constructor
  intro R S
  apply Subtype.ext
  apply Subtype.ext
  have hPa := rank_four_cross_axis_eq_one_of_common q P Q R.val hd R.property.1 R.property.2
  have hQa := rank_four_cross_axis_eq_one_of_common q Q P R.val hd.symm R.property.2 R.property.1
  have hR := CFSGPolarCommonNeighbourUnique.common_neighbour_eq_forced_sum
    (fixedQuadraticForm 2 q).polarBilin P.val Q.val R.val.val hd hPa hQa R.val.property.1
    R.property.1.2.1 R.property.2.2.1
    (cross_of_adjacent 0 q P R.val R.property.1) (cross_of_adjacent 0 q Q R.val R.property.2)
  have hS := CFSGPolarCommonNeighbourUnique.common_neighbour_eq_forced_sum
    (fixedQuadraticForm 2 q).polarBilin P.val Q.val S.val.val hd hPa hQa S.val.property.1
    S.property.1.2.1 S.property.2.2.1
    (cross_of_adjacent 0 q P S.val S.property.1) (cross_of_adjacent 0 q Q S.val S.property.2)
  exact hR.trans hS.symm

theorem rank_four_disjoint_commonNeighbours_card_le_one (q : CFSG.PrimePower)
    (P Q : SingularPlanes 0 q) (hd : Disjoint P.val Q.val) :
    Nat.card (CommonNeighbours 0 q P Q) ≤ 1 := by
  letI := rank_four_commonNeighbours_subsingleton q P Q hd
  let f : CommonNeighbours 0 q P Q → Fin 1 := fun _ => 0
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f
    (fun _ _ _ => Subsingleton.elim _ _)

def commonNeighbourCrossing (s : ℕ) (q : CFSG.PrimePower)
    (P Q : SingularPlanes s q) (R : CommonNeighbours s q P Q) : Crossing P.val Q.val :=
  ⟨R.val.val, R.val.property.1, R.property.1.2.1, R.property.2.2.1⟩

theorem disjoint_commonNeighbours_card_le (s : ℕ) (q : CFSG.PrimePower)
    (P Q : SingularPlanes s q) (hd : Disjoint P.val Q.val) :
    Nat.card (CommonNeighbours s q P Q) ≤ (q.order + 1) ^ 2 := by
  letI := crossing_finite P.val Q.val hd
  have hi : Function.Injective (commonNeighbourCrossing s q P Q) := by
    intro R S he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun T : Crossing P.val Q.val => T.val) he
  have hb := (Nat.card_le_card_of_injective (commonNeighbourCrossing s q P Q) hi).trans
    (crossing_card_le P.val Q.val P.property.1 Q.property.1 hd)
  simpa only [fixedField_card] using hb

def recognitionBound (s : ℕ) (q : CFSG.PrimePower) : ℕ :=
  if s = 0 then 1 else (q.order + 1) ^ 2

theorem disjoint_commonNeighbours_card_le_recognitionBound (s : ℕ) (q : CFSG.PrimePower)
    (P Q : SingularPlanes s q) (hd : Disjoint P.val Q.val) :
    Nat.card (CommonNeighbours s q P Q) ≤ recognitionBound s q := by
  by_cases hs : s = 0
  · subst s
    exact rank_four_disjoint_commonNeighbours_card_le_one q P Q hd
  · simpa only [recognitionBound, if_neg hs] using disjoint_commonNeighbours_card_le s q P Q hd

end SymmetricSubgroupAsymptotics.CFSGTwistedDDisjointCommonNeighbours
