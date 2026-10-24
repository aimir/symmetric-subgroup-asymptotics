import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWeylRootMembership
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLeadingHom
import SymmetricSubgroupAsymptotics.CFSGGradedQuadraticFirstLayer

/-! A positive Weyl-conjugated simple parameter of integer height greater
than one has trivial actual simple leading coordinates, in every field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveWordLeadingZero
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoCoordinateWeylRootMembership CFSGNormTwoCoordinateLeadingHom
open CFSGNormTwoCoordinateLeadingFactor CFSGNormTwoCoordinateHeight
open CFSGNormTwoGeckHeightSupport CFSGNormTwoGeckLatticeDegree
open CFSGGradedMatrixGroupFirstLayer CFSGGradedQuadraticFirstLayer
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

def positiveWord (K : Type) [Field K] (w : List (Fin r)) (j : Fin r) (t : K)
    (hpos : ∀i,0≤(wordRoot A hs hp b₀ s₀ w (s₀ j)).val i) :
    CFSGNormTwoGeckPositivePGroup.rootGroup A hs hp b₀ s₀ K false :=
  ⟨rootWord A hd hs hp ho K w j t,positive_word_mem A hd hs hp ho K w j t hpos⟩

theorem leadingHom_positiveWord (K : Type) [Field K] (w : List (Fin r)) (j : Fin r)
    (t : K) (hpos : ∀i,0≤(wordRoot A hs hp b₀ s₀ w (s₀ j)).val i)
    (hheight : 1<coordinateHeight (wordRoot A hs hp b₀ s₀ w (s₀ j)).val) :
    leadingHom A hd hs hp ho K (positiveWord A hd hs hp ho K w j t hpos)=1 := by
  have hg := word_conjugate_quadraticGrade A hs hp b₀ s₀ K w j t
  have hz := firstLayer_eq_zero_of_height_gt_one (latticeWeight A hs hp b₀)
    coordinateHeight.toAddMonoidHom _ _ hg hheight
  have hw : (coordinateHeight.toAddMonoidHom ∘ latticeWeight A hs hp b₀)=
      weight A hs hp b₀ coordinateHeight := by
    funext i
    cases i <;> simp [latticeWeight,weight,Function.comp_apply]
  rw [hw] at hz
  change firstLayer (weight A hs hp b₀ coordinateHeight) (rootWord A hd hs hp ho K w j t)=0 at hz
  change leadingCoordinates A hd hs hp ho K (rootWord A hd hs hp ho K w j t)=0
  funext i
  rw [←firstLayer_entry]
  change firstLayer (weight A hs hp b₀ coordinateHeight) (rootWord A hd hs hp ho K w j t)
    (Sum.inl (s₀ i))
    (Sum.inr (CFSGNormTwoGeckColumns.negativeIndex A hs hp (s₀ i)))=0
  rw [hz]
  rfl

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveWordLeadingZero
