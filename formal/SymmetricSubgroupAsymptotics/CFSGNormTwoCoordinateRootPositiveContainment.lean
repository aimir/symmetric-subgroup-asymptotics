import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateAllRootParameters
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootHeightSupport
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveHeightNormalForm
import SymmetricSubgroupAsymptotics.CFSGIntegralNormTwoSigns

/-! An original lattice-root subgroup lies in actual U precisely when
the root is positive. Negative integer-height coefficients cannot hide
inside U, independently of bad-characteristic torus eigenvalues. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootPositiveContainment
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGIntegerHeightSign
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCoordinateRootElementRange
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateRootHeightLeading
open CFSGNormTwoCoordinateRootBracketTransport CFSGNormTwoCoordinateRootCoefficientCoordinates
open CFSGNormTwoCoordinatePositiveRootGenerators CFSGNormTwoCoordinateRootHeightQuotient
open CFSGNormTwoCoordinateRootHeightSupport CFSGNormTwoCoordinatePositiveHeightNormalForm
open CFSGGradedQuadraticFirstCoefficient CFSGGradedMatrixSingleDegreeSpan
open CFSGNormTwoGeckColumns CFSGNormTwoCoordinateRootHeightCommutator CFSGIntegralNormTwoSigns
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
private abbrev CoordMat (K : Type) := Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K

theorem negative_height_root_not_positive (K : Type) [Field K] (k : Roots A)
    (hk : height k.val<0) : selectedRootElement A hd hs hp ho K k 1∉PositiveGroup A hd hs hp ho K := by
  intro hmem
  have ht : selectedRootElement A hd hs hp ho K k 1∈
      CFSGNormTwoCoordinateRootHeightFiltration.heightTail A hd hs hp ho K 1 := by
    rw [heightTail_one_eq_positive]
    exact hmem
  have hz := heightTail_degreePart_zero A hd hs hp ho K 1 (height k.val)
    (by decide) (by omega) _ ht
  have hfirst : degreePart (heightWeight A hd hs hp ho) (height k.val)
      (selectedRootElement A hd hs hp ho K k 1 : CoordMat A hd hs hp ho K)=
        selectedFieldCoefficient A hd hs hp ho K k := by
    rw [selectedRootElement_expansion]
    simpa only [one_smul,one_pow] using
      (degreePart_quadratic (heightWeight A hd hs hp ho) (height k.val)
        (selectedFieldCoefficient A hd hs hp ho K k)
        (selectedSecondCoefficient A hd hs hp ho K k)
        (first_height_support A hd hs hp ho K k) (second_height_support A hd hs hp ho K k)
        (by omega) (by omega))
  rw [map_sub,hfirst,degreePart_one_zero _ _ (by omega : height k.val≠0),sub_zero] at hz
  exact selectedFieldCoefficient_ne_zero A hd hs hp ho K k hz

theorem rootSubgroup_le_positive_iff (K : Type) [Field K] (k : Roots A) :
    rootSubgroup A hd hs hp ho K k≤PositiveGroup A hd hs hp ho K↔∀i,0≤k.val i := by
  constructor
  · intro hsub
    by_contra hpos
    have heven (i : Fin r) : Even (A i i) := by rw [hd i];exact ⟨1,rfl⟩
    have hn := (norm_two_coordinates_one_sign A hs hp heven ho k.val k.property).resolve_left hpos
    have hnegative : ∀i,0≤(negativeIndex A hs hp k).val i := by
      intro i
      simpa only [negative_val,Pi.neg_apply] using neg_nonneg.mpr (hn i)
    have hh := positive_root_height_pos A (negativeIndex A hs hp k) hnegative
    rw [negative_val,height_neg] at hh
    exact negative_height_root_not_positive A hd hs hp ho K k (by omega)
      (hsub (selectedRootElement_mem A hd hs hp ho K k 1))
  · exact positive_root_subgroup_le A hd hs hp ho K k

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootPositiveContainment
