import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootHeightLeading

/-! Exact leading coefficients for any positive integral root functional.
The original lattice support is transported before reduction to the
field. This retains higher quadratic corrections and applies to the
outside grading, whose zero roots prevent use of ordinary root height. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateFunctionalRootLeading
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckLatticeDegree CFSGNormTwoCoordinateRootSubgroup
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateRootHeightLeading
open CFSGNormTwoCoordinateRootBracketTransport CFSGNormTwoCoordinateRootCoefficientCoordinates
open CFSGGradedQuadraticUnit CFSGGradedMatrixSingleDegreeSpan
open CFSGGradedMatrixHighLayerProducts
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "ell" => latticeWeight A hs hp b₀
private abbrev Mat (K : Type) := Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K

theorem selected_functional_cut_and_leading (K : Type) [Field K]
    (f : (Fin r→ℤ)→+ℤ) (k : Roots A) (hk : 0<f k.val) (a : K) :
    BelowCut (f∘ell) (f k.val)
      ((selectedRootElement A hd hs hp ho K k a : Mat A hd hs hp ho K)-1) ∧
      degreePart (f∘ell) (f k.val)
        ((selectedRootElement A hd hs hp ho K k a : Mat A hd hs hp ho K)-1)=
        a • selectedFieldCoefficient A hd hs hp ho K k := by
  have hdev : (selectedRootElement A hd hs hp ho K k a : Mat A hd hs hp ho K)-1=
      a • selectedFieldCoefficient A hd hs hp ho K k+
        a^2 • selectedSecondCoefficient A hd hs hp ho K k := by
    rw [selectedRootElement_expansion]
    abel
  have hfirst := support_apply_height ell k.val f _
    (selectedFieldCoefficient_support A hd hs hp ho K k)
  have hsecond := support_apply_height ell (k.val+k.val) f _
    (selectedSecondCoefficient_support A hd hs hp ho K k)
  simp only [map_add] at hsecond
  simp only [hdev]
  constructor
  · apply belowCut_add
    · intro i j hij
      have hne : (f∘ell) i≠(f∘ell) j+f k.val := by omega
      rw [Matrix.smul_apply,hfirst i j hne,smul_zero]
    · intro i j hij
      have hne : (f∘ell) i≠(f∘ell) j+(f k.val+f k.val) := by omega
      rw [Matrix.smul_apply,hsecond i j hne,smul_zero]
  · rw [map_add,map_smul,map_smul,
      degreePart_eq _ _ _ hfirst,
      degreePart_zero_of_other _ (f k.val) (f k.val+f k.val) _ hsecond (by omega),
      smul_zero,add_zero]

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateFunctionalRootLeading
