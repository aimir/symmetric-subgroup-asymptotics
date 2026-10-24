import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateReflectionSigns
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylWordDegree

/-! Coordinate reflections change only their own root coordinate. A word
avoiding a coordinate therefore preserves it; a positive value in that
coordinate forces the resulting norm-two root to be positive. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOutsideWordPositive
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckSignedRootColumns
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem wordRoot_outside_coordinate (w : List (Fin r)) (k : Roots A) (j : Fin r)
    (hw : ∀i∈w,i≠j) : (wordRoot A hs hp b₀ s₀ w k).val j=k.val j := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    have hi : i≠j := hw i List.mem_cons_self
    have ht : ∀a∈w,a≠j := fun a ha=>hw a (List.mem_cons_of_mem i ha)
    have hz : (s₀ i : Roots A).val j=0 := by
      change (Pi.single i (1:ℤ) : Fin r→ℤ) j=0
      simp [Ne.symm hi]
    change (((rootPairing A hs hp).reflectionPerm (s₀ i)
      (wordRoot A hs hp b₀ s₀ w k)).val) j=k.val j
    rw [CFSGNormTwoGeckSignedRootColumns.reflection_val]
    simp only [Pi.sub_apply,Pi.smul_apply,hz,smul_zero,sub_zero]
    exact ih ht

theorem wordRoot_nonnegative_of_outside_positive (w : List (Fin r)) (k : Roots A)
    (j : Fin r) (hw : ∀i∈w,i≠j) (hk : 0<k.val j) :
    ∀i,0≤(wordRoot A hs hp b₀ s₀ w k).val i := by
  have hj : 0<(wordRoot A hs hp b₀ s₀ w k).val j := by
    rw [wordRoot_outside_coordinate A hd hs hp ho w k j hw]
    exact hk
  rcases CFSGIntegralNormTwoSigns.norm_two_coordinates_one_sign A hs hp
    (fun i=>by rw [hd i];exact even_two) ho
    (wordRoot A hs hp b₀ s₀ w k).val (wordRoot A hs hp b₀ s₀ w k).property with h|h
  · exact h
  · have hbad := h j
    omega

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOutsideWordPositive
