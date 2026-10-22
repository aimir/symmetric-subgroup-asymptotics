import SymmetricSubgroupAsymptotics.CFSGFiniteOrderedFamilyLeading
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHeightLayerFactorization
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootHeightLeading

/-! Leading coefficients and uniqueness for the SAME exact-height
ordered word used in the proved actual layer factorization. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateExactHeightWordLeading
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGIntegerHeightSign
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateRootBracketTransport
open CFSGNormTwoCoordinateSelectedRootAdditive
open CFSGNormTwoCoordinateRootCoefficientCoordinates CFSGNormTwoCoordinateRootHeightLeading
open CFSGNormTwoCoordinateRootHeightQuotient CFSGNormTwoCoordinateExactHeightLayer
open CFSGNormTwoCoordinateHeightLayerFactorization
open CFSGFiniteQuotientFamilyProduct CFSGFiniteOrderedFamilyLeading
open CFSGGradedMatrixSingleDegreeSpan CFSGGradedMatrixHighLayerProducts
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
private abbrev CoordMat (K : Type) := Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K

theorem exactHeightWord_coe (K : Type) [Field K] (h : ℤ) (c : ExactHeightRoot A h→K) :
    (exactHeightWord A hd hs hp ho K h c : (CoordMat A hd hs hp ho K)ˣ)=
      orderedFamilyProduct (fun k : ExactHeightRoot A h=>
        selectedRootElement A hd hs hp ho K k.val.val (c k)) := by
  classical
  change (PositiveGroup A hd hs hp ho K).subtype
    (orderedFamilyProduct (fun k : ExactHeightRoot A h=>
      positiveRootParameterHom A hd hs hp ho K k.val.val k.val.property (Multiplicative.ofAdd (c k))))=_
  rw [map_orderedFamilyProduct]
  rfl

theorem exactHeightWord_cut_and_leading (K : Type) [Field K] (h : ℤ) (hh : 0<h)
    (c : ExactHeightRoot A h→K) :
    BelowCut (heightWeight A hd hs hp ho) h
      (((exactHeightWord A hd hs hp ho K h c).val : CoordMat A hd hs hp ho K)-1) ∧
      degreePart (heightWeight A hd hs hp ho) h
        (((exactHeightWord A hd hs hp ho K h c).val : CoordMat A hd hs hp ho K)-1)=
        ∑k,c k • selectedFieldCoefficient A hd hs hp ho K k.val.val := by
  classical
  have hroot (k : ExactHeightRoot A h) :
      BelowCut (heightWeight A hd hs hp ho) h
        ((selectedRootElement A hd hs hp ho K k.val.val (c k) : CoordMat A hd hs hp ho K)-1) ∧
      degreePart (heightWeight A hd hs hp ho) h
        ((selectedRootElement A hd hs hp ho K k.val.val (c k) : CoordMat A hd hs hp ho K)-1)=
        c k • selectedFieldCoefficient A hd hs hp ho K k.val.val := by
    have hk : 0<height k.val.val.val := by rw [k.property];exact hh
    simpa only [k.property] using selected_root_cut_and_leading A hd hs hp ho K k.val.val hk (c k)
  rw [exactHeightWord_coe]
  have hl := finite_ordered_leading (heightWeight A hd hs hp ho) h hh
    (fun k : ExactHeightRoot A h=>selectedRootElement A hd hs hp ho K k.val.val (c k))
    (fun k=>(hroot k).1)
  refine ⟨hl.1,?_⟩
  rw [hl.2]
  exact Finset.sum_congr rfl (fun k _=>(hroot k).2)

theorem exactHeightWord_zero (K : Type) [Field K] (h : ℤ) :
    exactHeightWord A hd hs hp ho K h (fun _=>0)=1 := by
  classical
  apply (PositiveGroup A hd hs hp ho K).subtype_injective
  change (exactHeightWord A hd hs hp ho K h (fun _=>0) : (CoordMat A hd hs hp ho K)ˣ)=1
  rw [exactHeightWord_coe]
  simp [selectedRootElement_zero,orderedFamilyProduct]

theorem exactHeightWord_injective (K : Type) [Field K] (h : ℤ) (hh : 0<h) :
    Function.Injective (exactHeightWord A hd hs hp ho K h) := by
  classical
  intro c d heq
  have he := congrArg (fun x : PositiveGroup A hd hs hp ho K=>
    degreePart (heightWeight A hd hs hp ho) h ((x.val : CoordMat A hd hs hp ho K)-1)) heq
  dsimp only at he
  rw [(exactHeightWord_cut_and_leading A hd hs hp ho K h hh c).2,
    (exactHeightWord_cut_and_leading A hd hs hp ho K h hh d).2] at he
  exact root_family_coefficients_unique A hd hs hp ho K
    (fun k : ExactHeightRoot A h=>k.val.val)
    (fun _ _ h=>Subtype.ext (Subtype.ext h)) c d he

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateExactHeightWordLeading
