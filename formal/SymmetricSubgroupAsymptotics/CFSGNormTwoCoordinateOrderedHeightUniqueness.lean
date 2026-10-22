import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootHeightLeading
import Mathlib.Algebra.BigOperators.Fin

/-! Ordered products in ANY single positive height have unique actual
root parameters over every field. Their height coefficient is the sum
of the primitive root coefficients, and distinct INTEGER lattice degrees
recover every parameter. No ordered-product surjectivity is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOrderedHeightUniqueness
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGIntegerHeightSign
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateRootBracketTransport
open CFSGNormTwoCoordinateRootCoefficientCoordinates CFSGNormTwoCoordinateRootHeightLeading
open CFSGGradedMatrixSingleDegreeSpan CFSGGradedMatrixHighLayerProducts
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
private abbrev CoordMat (K : Type) := Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K

def orderedRootWord (K : Type) [Field K] {m : ℕ} (f : Fin m→Roots A) (c : Fin m→K) :
    (CoordMat A hd hs hp ho K)ˣ :=
  (List.ofFn (fun i : Fin m=>selectedRootElement A hd hs hp ho K (f i) (c i))).prod

theorem ordered_same_height_cut_and_leading (K : Type) [Field K] {m : ℕ}
    (f : Fin m→Roots A) (h : ℤ) (hh : 0<h) (hheight : ∀i,height (f i).val=h) (c : Fin m→K) :
    BelowCut (heightWeight A hd hs hp ho) h
      ((orderedRootWord A hd hs hp ho K f c : CoordMat A hd hs hp ho K)-1) ∧
      degreePart (heightWeight A hd hs hp ho) h
        ((orderedRootWord A hd hs hp ho K f c : CoordMat A hd hs hp ho K)-1)=
        ∑i,c i • selectedFieldCoefficient A hd hs hp ho K (f i) := by
  have hroot (i : Fin m) :
      BelowCut (heightWeight A hd hs hp ho) h
        ((selectedRootElement A hd hs hp ho K (f i) (c i) : CoordMat A hd hs hp ho K)-1) ∧
      degreePart (heightWeight A hd hs hp ho) h
        ((selectedRootElement A hd hs hp ho K (f i) (c i) : CoordMat A hd hs hp ho K)-1)=
        c i • selectedFieldCoefficient A hd hs hp ho K (f i) := by
    have hpos : 0<height (f i).val := by rw [hheight i];exact hh
    simpa only [hheight i] using selected_root_cut_and_leading A hd hs hp ho K (f i) hpos (c i)
  have hpiece (i : Fin m) := (hroot i).2
  have hl := ordered_leading_layer (heightWeight A hd hs hp ho) h hh
    (List.ofFn (fun i : Fin m=>selectedRootElement A hd hs hp ho K (f i) (c i))) (by
      intro u hu
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hu
      exact (hroot i).1)
  simpa only [orderedRootWord,List.map_ofFn,List.sum_ofFn,Function.comp_apply,hpiece] using hl

theorem ordered_same_height_injective (K : Type) [Field K] {m : ℕ}
    (f : Fin m→Roots A) (hf : Function.Injective f)
    (h : ℤ) (hh : 0<h) (hheight : ∀i,height (f i).val=h) :
    Function.Injective (orderedRootWord A hd hs hp ho K f) := by
  intro c d heq
  have hc := (ordered_same_height_cut_and_leading A hd hs hp ho K f h hh hheight c).2
  have hd' := (ordered_same_height_cut_and_leading A hd hs hp ho K f h hh hheight d).2
  have he := congrArg (fun u : (CoordMat A hd hs hp ho K)ˣ=>
    degreePart (heightWeight A hd hs hp ho) h ((u : CoordMat A hd hs hp ho K)-1)) heq
  dsimp only at he
  rw [hc,hd'] at he
  exact root_family_coefficients_unique A hd hs hp ho K f hf c d he

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOrderedHeightUniqueness
