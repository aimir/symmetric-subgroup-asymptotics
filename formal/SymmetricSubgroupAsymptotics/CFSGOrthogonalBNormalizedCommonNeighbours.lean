import SymmetricSubgroupAsymptotics.CFSGOrthogonalBResidualCorrection
import SymmetricSubgroupAsymptotics.CFSGPolarCommonPointPlanes
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBNonzeroSingularCount
import SymmetricSubgroupAsymptotics.CFSGProjectiveFibreCardBound
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBDisjointCommonNeighbours

/-! Actual common neighbours in the normalized original natural space.
The residual cone maps to planes through e0, with proportional fibres;
no residual classical-model recognition or cone quotient formula occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBNormalizedCommonNeighbours
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBUnipotent CFSGOrthogonalBIntrinsicLongRoots
open CFSGOrthogonalBPlaneFamilyAction CFSGOrthogonalBResidualCorrection
open CFSGOrthogonalBTailCoordinates CFSGPolarCommonPointPlanes CFSGOrthogonalBNonzeroSingularCount
variable {K : Type} [Field K] [Finite K]

def firstVector (s : ℕ) : Index (s + 3) → K := positiveVector s 0
def secondVector (s : ℕ) : Index (s + 3) → K := positiveVector s (secondIndex s)

omit [Finite K] in
private theorem first_ne_zero (s : ℕ) : firstVector (K := K) s ≠ 0 := by
  intro he
  have h := congrFun he (pos (s + 3) 0)
  simp [firstVector, positiveVector] at h

omit [Finite K] in
private theorem positive_pairing_zero (s : ℕ) (i j : Fin (s + 3)) :
    (gram K (s + 3)).toBilin' (positiveVector (K := K) s i) (positiveVector s j) = 0 := by
  rw [positiveVector_pairing]
  simp [positiveVector, pos, neg]

def firstPlane (s : ℕ) : SingularPlanes (K := K) s :=
  ⟨standardRootPlane s, standardRootPlane_finrank s, standardRootPlane_totallySingular s⟩

omit [Finite K] in
theorem companion_not_first (s : ℕ) (w : Index (s + 3) → K)
    (hc : (gram K (s + 3)).toBilin' w (secondVector s) ≠ 0) (a : K) :
    w ≠ a • firstVector (K := K) s := by
  intro he
  apply hc
  rw [he, map_smul, LinearMap.smul_apply]
  dsimp only [firstVector, secondVector]
  rw [positive_pairing_zero]
  exact smul_zero a

def secondPlane (s : ℕ) (w : Index (s + 3) → K)
    (hw : (gram K (s + 3)).toBilin' w w = 0)
    (hwu : (gram K (s + 3)).toBilin' w (firstVector s) = 0)
    (hc : (gram K (s + 3)).toBilin' w (secondVector s) ≠ 0) : SingularPlanes (K := K) s :=
  ⟨pairPlane (K := K) (firstVector s) w, pairPlane_finrank _ _ (first_ne_zero s) (companion_not_first s w hc),
    pairPlane_singular _ _ _ (positive_pairing_zero s 0 0) hw
      ((gram_pairing_symmetric (s + 3) _ _).trans hwu) hwu⟩

theorem residual_not_firstPlane (s : ℕ) (w : Index (s + 3) → K)
    (z : NonzeroCone K (s + 1)) : residualMap K s w z.val ∉ (firstPlane (K := K) s).val := by
  intro hz
  obtain ⟨a, b, he⟩ := Submodule.mem_span_pair.mp hz
  have h := congrArg (twiceTailRestriction K s) he
  rw [map_add, map_smul, map_smul, twiceTailRestriction_first, twiceTailRestriction_second,
    smul_zero, smul_zero, zero_add, residualMap_leftInverse] at h
  exact z.property.2 h.symm

theorem residual_not_secondPlane (s : ℕ) (w : Index (s + 3) → K)
    (hw : (gram K (s + 3)).toBilin' w w = 0)
    (hwu : (gram K (s + 3)).toBilin' w (firstVector s) = 0)
    (hc : (gram K (s + 3)).toBilin' w (secondVector s) ≠ 0)
    (z : NonzeroCone K (s + 1)) : residualMap K s w z.val ∉ (secondPlane s w hw hwu hc).val := by
  intro hz
  obtain ⟨a, b, he⟩ := Submodule.mem_span_pair.mp hz
  have hp := congrArg ((gram K (s + 3)).toBilin' (secondVector s)) he
  dsimp only [firstVector, secondVector] at hp
  rw [map_add, map_smul, map_smul, positive_pairing_zero, smul_zero, zero_add,
    residualMap_perp_positive K s w z.val (secondIndex s) (Or.inr rfl)] at hp
  have hcross : (gram K (s + 3)).toBilin' (secondVector s) w ≠ 0 :=
    fun hn => hc ((gram_pairing_symmetric (s + 3) w _).trans hn)
  have hb : b = 0 := (mul_eq_zero.mp hp).resolve_right hcross
  rw [hb, zero_smul, add_zero] at he
  have h := congrArg (twiceTailRestriction K s) he
  dsimp only [firstVector] at h
  rw [map_smul, twiceTailRestriction_first, smul_zero, residualMap_leftInverse] at h
  exact z.property.2 h.symm

def neighbour (s : ℕ) (w : Index (s + 3) → K) (z : NonzeroCone K (s + 1)) :
    SingularPlanes (K := K) s := by
  let u : Index (s + 3) → K := firstVector s
  let v := residualMap K s w z.val
  have hnot (a : K) : v ≠ a • u := by
    intro he
    have h := congrArg (twiceTailRestriction K s) he
    dsimp only [u, v, firstVector] at h
    rw [map_smul, twiceTailRestriction_first, smul_zero, residualMap_leftInverse] at h
    exact z.property.2 h
  have hv : (gram K (s + 3)).toBilin' v v = 0 :=
    (residualMap_norm K s w z.val).trans z.property.1
  have huv : (gram K (s + 3)).toBilin' u v = 0 :=
    residualMap_perp_positive K s w z.val 0 (Or.inl rfl)
  exact ⟨pairPlane (K := K) u v, pairPlane_finrank u v (first_ne_zero s) hnot,
    pairPlane_singular _ u v (positive_pairing_zero s 0 0) hv huv
      ((gram_pairing_symmetric (s + 3) v u).trans huv)⟩

theorem first_adjacent (s : ℕ) (w : Index (s + 3) → K) (z : NonzeroCone K (s + 1)) :
    PlaneAdjacent s (firstPlane (K := K) s).val (neighbour s w z).val := by
  apply pairPlane_adjacent_data (gram K (s + 3)).toBilin' (gram_pairing_symmetric (s + 3))
    _ (firstPlane (K := K) s).property.1 (firstPlane (K := K) s).property.2
    (firstVector s) (residualMap K s w z.val)
    (Submodule.subset_span (Or.inl rfl)) (first_ne_zero s)
    ((residualMap_norm K s w z.val).trans z.property.1) (residual_not_firstPlane s w z)
  intro x hx
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    residualMap_perp_positive K s w z.val 0 (Or.inl rfl),
    residualMap_perp_positive K s w z.val (secondIndex s) (Or.inr rfl), smul_zero, add_zero]

theorem second_adjacent (s : ℕ) (w : Index (s + 3) → K)
    (hw : (gram K (s + 3)).toBilin' w w = 0)
    (hwu : (gram K (s + 3)).toBilin' w (firstVector s) = 0)
    (hc : (gram K (s + 3)).toBilin' w (secondVector s) ≠ 0) (z : NonzeroCone K (s + 1)) :
    PlaneAdjacent s (secondPlane s w hw hwu hc).val (neighbour s w z).val := by
  apply pairPlane_adjacent_data (gram K (s + 3)).toBilin' (gram_pairing_symmetric (s + 3))
    _ (secondPlane s w hw hwu hc).property.1 (secondPlane s w hw hwu hc).property.2
    (firstVector s) (residualMap K s w z.val)
    (Submodule.subset_span (Or.inl rfl)) (first_ne_zero s)
    ((residualMap_norm K s w z.val).trans z.property.1) (residual_not_secondPlane s w hw hwu hc z)
  intro x hx
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
  dsimp only [firstVector]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    residualMap_perp_positive K s w z.val 0 (Or.inl rfl),
    residualMap_perp_companion K s w hc z.val, smul_zero, add_zero]

def commonNeighbourMap (s : ℕ) (w : Index (s + 3) → K)
    (hw : (gram K (s + 3)).toBilin' w w = 0)
    (hwu : (gram K (s + 3)).toBilin' w (firstVector s) = 0)
    (hc : (gram K (s + 3)).toBilin' w (secondVector s) ≠ 0) :
    NonzeroCone K (s + 1) → CommonNeighbours s (firstPlane s) (secondPlane s w hw hwu hc) :=
  fun z => ⟨neighbour s w z, first_adjacent s w z, second_adjacent s w hw hwu hc z⟩

theorem normalized_cone_le_common (h2 : (2 : K) ≠ 0) (s : ℕ) (w : Index (s + 3) → K)
    (hw : (gram K (s + 3)).toBilin' w w = 0)
    (hwu : (gram K (s + 3)).toBilin' w (firstVector s) = 0)
    (hc : (gram K (s + 3)).toBilin' w (secondVector s) ≠ 0) :
    Nat.card K ^ (2 * (s + 1)) - 1 ≤
      Nat.card (CommonNeighbours s (firstPlane s) (secondPlane s w hw hwu hc)) * Nat.card K := by
  rw [← nonzero_singular_card K (s + 1) h2]
  apply CFSGProjectiveFibreCardBound.card_le_mul (fun z : NonzeroCone K (s + 1) => z.val)
    Subtype.val_injective (commonNeighbourMap s w hw hwu hc)
  intro z z' he
  have hp : pairPlane (K := K) (firstVector s) (residualMap K s w z.val) =
      pairPlane (K := K) (firstVector s) (residualMap K s w z'.val) :=
    congrArg (fun T : CommonNeighbours s (firstPlane s) (secondPlane s w hw hwu hc) => T.val.val) he
  exact pairPlane_eq_implies_proportional _ (residualMap K s w) (twiceTailRestriction K s)
    (residualMap_leftInverse K s w) (twiceTailRestriction_first K s) z.val z'.val hp

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBNormalizedCommonNeighbours
