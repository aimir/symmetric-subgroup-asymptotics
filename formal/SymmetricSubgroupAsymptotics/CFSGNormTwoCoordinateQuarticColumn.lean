import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckDoubleRootSupport
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNegativeColumns
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckCartanDegreeAction
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCartan
import SymmetricSubgroupAsymptotics.CFSGGeckSerreRepresentation

/-! The ONE nonzero column of the actual adjacent-root quartic:
([E_i,E_j] F_j)^2 v_-i = -v_i. This computes genuine Geck columns;
no root-space recognition or natural-Lie injectivity is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateQuarticColumn
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoRootStrings
open CFSGNormTwoGeckColumns CFSGNormTwoGeckNegativeColumns
open CFSGNormTwoGeckCartanDegreeAction
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
private abbrev MatQ := Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) ℚ
private abbrev VecQ := ((b₀).support⊕Roots A)→ℚ

theorem E_negative_other (i j : Fin r) (hij : i≠j) (hA : A i j= -1) :
    (RootPairing.GeckConstruction.e (s₀ i) : MatQ A hd hs hp ho)*ᵥ
      RootPairing.GeckConstruction.v b₀ (negativeIndex A hs hp (s₀ j))=0 := by
  apply E_v_zero A hs hp b₀ (s₀ i) (negativeIndex A hs hp (s₀ j))
  · intro he
    have hh := congrArg Subtype.val he
    rw [negative_val,negative_val] at hh
    apply hij
    apply (s₀).injective
    apply Subtype.ext
    apply Subtype.ext
    exact (neg_injective hh).symm
  · rintro ⟨k,hk⟩
    have hbad := pairing_of_root_add A hs hp hk
    rw [negative_val,map_neg] at hbad
    have hp' : integerPairing A (s₀ i : Roots A).val (s₀ j : Roots A).val= -1 := by
      change Matrix.toBilin' A (Pi.single i (1:ℤ)) (Pi.single j (1:ℤ))= -1
      rw [Matrix.toBilin'_single]
      exact hA
    rw [hp'] at hbad
    norm_num at hbad

theorem quartic_negative_column (i j : Fin r) (hij : i≠j)
    (hA : A i j= -1) (hA' : A j i= -1) :
    ((⁅(RootPairing.GeckConstruction.e (s₀ i) : MatQ A hd hs hp ho),RootPairing.GeckConstruction.e (s₀ j)⁆ *
      RootPairing.GeckConstruction.f (s₀ j))^2)*ᵥ
        RootPairing.GeckConstruction.v b₀ (negativeIndex A hs hp (s₀ i))=
          -RootPairing.GeckConstruction.v b₀ (s₀ i) := by
  let X : MatQ A hd hs hp ho := RootPairing.GeckConstruction.e (s₀ i)
  let Y : MatQ A hd hs hp ho := RootPairing.GeckConstruction.e (s₀ j)
  let Z : MatQ A hd hs hp ho := RootPairing.GeckConstruction.f (s₀ j)
  let C := X*Y-Y*X
  let vni : VecQ A hd hs hp ho := RootPairing.GeckConstruction.v b₀ (negativeIndex A hs hp (s₀ i))
  let vnj : VecQ A hd hs hp ho := RootPairing.GeckConstruction.v b₀ (negativeIndex A hs hp (s₀ j))
  let vi : VecQ A hd hs hp ho := RootPairing.GeckConstruction.v b₀ (s₀ i)
  let ui : VecQ A hd hs hp ho := RootPairing.GeckConstruction.u (s₀ i)
  let uj : VecQ A hd hs hp ho := RootPairing.GeckConstruction.u (s₀ j)
  have hYni : Y*ᵥvni=0 := E_negative_other A hd hs hp ho j i (Ne.symm hij) hA'
  have hXnj : X*ᵥvnj=0 := E_negative_other A hd hs hp ho i j hij hA
  have hXni : X*ᵥvni=ui := E_v_negative A hs hp b₀ (s₀ i)
  have hYnj : Y*ᵥvnj=uj := E_v_negative A hs hp b₀ (s₀ j)
  have hZui : Z*ᵥui=vnj := by
    dsimp only [Z,ui,vnj]
    rw [F_u A hs hp b₀,coordinate_cartan,hA']
    norm_num
  have hZuj : Z*ᵥuj=vnj+vnj := by
    dsimp only [Z,uj,vnj]
    rw [F_u A hs hp b₀,coordinate_cartan,hd j]
    norm_num [two_smul]
  have hXuj : X*ᵥuj=vi := by
    dsimp only [X,uj,vi]
    rw [E_u A hs hp b₀,coordinate_cartan,hA]
    norm_num
  have hHni : RootPairing.GeckConstruction.h (s₀ j)*ᵥvni=vni := by
    rw [cartan_eq_character_diagonal A hs hp b₀]
    dsimp only [vni,RootPairing.GeckConstruction.v]
    rw [Matrix.diagonal_mulVec_single]
    change (Pi.single (Sum.inr (negativeIndex A hs hp (s₀ i)))
      ((integerPairing A (negativeIndex A hs hp (s₀ i)).val (s₀ j : Roots A).val:ℚ)*1) :
        VecQ A hd hs hp ho)=_
    have hp' : integerPairing A (negativeIndex A hs hp (s₀ i)).val (s₀ j : Roots A).val=1 := by
      rw [negative_val,map_neg,LinearMap.neg_apply]
      change -Matrix.toBilin' A (Pi.single i (1:ℤ)) (Pi.single j (1:ℤ))=1
      rw [Matrix.toBilin'_single,hA]
      norm_num
    rw [hp']
    norm_num
  have hYZ : Y*ᵥ(Z*ᵥvni)=vni := by
    have he := congrArg (fun M=>M*ᵥvni)
      (RootPairing.GeckConstruction.lie_e_f_same (b:=b₀) (s₀ j))
    change (Y*Z-Z*Y)*ᵥvni=RootPairing.GeckConstruction.h (s₀ j)*ᵥvni at he
    rw [Matrix.sub_mulVec,←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,hYni,
      Matrix.mulVec_zero,sub_zero,hHni] at he
    exact he
  have hXZ : X*ᵥ(Z*ᵥvni)=vnj := by
    have he := RootPairing.GeckConstruction.lie_e_f_ne (b:=b₀) ((s₀).injective.ne hij)
    change X*Z-Z*X=0 at he
    rw [Matrix.mulVec_mulVec,sub_eq_zero.mp he,←Matrix.mulVec_mulVec,hXni,hZui]
  have hfirst : C*ᵥ(Z*ᵥvni)=ui-uj := by
    dsimp only [C]
    rw [Matrix.sub_mulVec,←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,hYZ,hXZ,hXni,hYnj]
  have hlast : C*ᵥvnj=vi := by
    dsimp only [C]
    rw [Matrix.sub_mulVec,←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,hYnj,hXnj,
      Matrix.mulVec_zero,sub_zero,hXuj]
  change (C*Z)^2*ᵥvni= -vi
  simp only [pow_two,←Matrix.mulVec_mulVec]
  rw [hfirst,Matrix.mulVec_sub,hZui,hZuj]
  have hv : vnj-(vnj+vnj)= -vnj := by abel
  rw [hv,Matrix.mulVec_neg,hlast]

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateQuarticColumn
