import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSelectedRootLine
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRaisedRoot

/-! Actual simple-versus-positive-root brackets have integral UNIT
coefficients on the original selected root lines. Genuine root-string
Jacobi gives inverse coefficients; actual primitive integer matrices
prove both coefficients integral before reduction to any field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootBracketUnit
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoGeckNegativeLatticeDegree CFSGNormTwoGeckRationalAdjointStrings
open CFSGNormTwoGeckRationalWeylCollecting CFSGNormTwoCoordinateRootWordString
open CFSGNormTwoCoordinateSelectedRootLine CFSGNormTwoCoordinateRaisedRoot
open CFSGGradedMatrixSupport CFSGGradedMatrixLieDegree
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀
private abbrev CoordMat (K : Type) := Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K
local notation "MatQ" => CoordMat A hd hs hp ho ℚ
local notation "MatZ" => CoordMat A hd hs hp ho ℤ
local notation "ell" => latticeWeight A hs hp b₀

theorem simple_root_bracket_sign (k : Roots A) (hk : ∀t,0≤k.val t) (i : Fin r)
    (hpair : integerPairing A k.val (s₀ i:Roots A).val= -1) :
    ∃ε : ℤ,(ε=1 ∨ ε= -1) ∧
      ⁅fieldRoot D ℚ false i,selectedCoefficient A hd hs hp ho k⁆=
        (ε:ℚ) • selectedCoefficient A hd hs hp ho (raisedRoot A hd hs hp ho k i hpair) := by
  let g := raisedRoot A hd hs hp ho k i hpair
  let X : MatQ := selectedCoefficient A hd hs hp ho k
  let Y : MatQ := selectedCoefficient A hd hs hp ho g
  have hXmem : X∈RootPairing.GeckConstruction.lieAlgebra b₀ :=
    selectedCoefficient_mem A hd hs hp ho k
  have hYmem : Y∈RootPairing.GeckConstruction.lieAlgebra b₀ :=
    selectedCoefficient_mem A hd hs hp ho g
  have hXdeg : Supported ell (fun v=>v+k.val) X := selectedCoefficient_degree A hd hs hp ho k
  have hYdeg : Supported ell (fun v=>v+g.val) Y := selectedCoefficient_degree A hd hs hp ho g
  have hEmem : fieldRoot D ℚ false i∈RootPairing.GeckConstruction.lieAlgebra b₀ := by
    rw [rational_E_eq]
    exact RootPairing.GeckConstruction.e_mem_lieAlgebra (s₀ i)
  have hFmem : fieldRoot D ℚ true i∈RootPairing.GeckConstruction.lieAlgebra b₀ := by
    rw [rational_F_eq]
    exact RootPairing.GeckConstruction.f_mem_lieAlgebra (s₀ i)
  have hEdeg := field_E_lattice_support A hs hp b₀ s₀ ℚ i
  have hFdeg : Supported ell (fun v=>v+ -(s₀ i:Roots A).val) (fieldRoot D ℚ true i) := by
    rw [rational_F_eq]
    simpa only [sub_eq_add_neg] using rational_F_lattice_support A hs hp b₀ (s₀ i)
  have hraiseDeg : Supported ell (fun v=>v+g.val) ⁅fieldRoot D ℚ false i,X⁆ := by
    apply supported_congr (supported_lie ell (s₀ i:Roots A).val k.val _ _ hEdeg hXdeg)
    intro v
    change v+((s₀ i:Roots A).val+k.val)=v+(k.val+(s₀ i:Roots A).val)
    abel
  have hlowerDeg : Supported ell (fun v=>v+k.val) ⁅fieldRoot D ℚ true i,Y⁆ := by
    apply supported_congr (supported_lie ell (-(s₀ i:Roots A).val) g.val _ _ hFdeg hYdeg)
    intro v
    change v+(-(s₀ i:Roots A).val+(k.val+(s₀ i:Roots A).val))=v+k.val
    abel
  obtain ⟨c,hc⟩ := mem_selected_line A hd hs hp ho g _
    ((RootPairing.GeckConstruction.lieAlgebra b₀).lie_mem hEmem hXmem) hraiseDeg
  obtain ⟨d,hd'⟩ := mem_selected_line A hd hs hp ho k _
    ((RootPairing.GeckConstruction.lieAlgebra b₀).lie_mem hFmem hYmem) hlowerDeg
  have hc' : ⁅fieldRoot D ℚ false i,X⁆=c • Y := hc
  have hd'' : ⁅fieldRoot D ℚ true i,Y⁆=d • X := hd'
  have hback : ⁅fieldRoot D ℚ true i,⁅fieldRoot D ℚ false i,X⁆⁆=X :=
    selected_lowering_after_raising A hd hs hp ho k hk i hpair
  rw [hc',lie_smul,hd'',smul_smul] at hback
  have hXne : X≠0 := selectedCoefficient_ne_zero A hd hs hp ho k
  have hprod : c*d=1 := by
    have hz : (c*d-1) • X=0 := by rw [sub_smul,one_smul,hback,sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hXne)
  let M : MatZ := ⁅CFSGGeckIntegralMatrices.E b₀ (s₀ i),integerSelectedCoefficient A hd hs hp ho k⁆
  let N : MatZ := ⁅CFSGGeckIntegralMatrices.F b₀ (s₀ i),integerSelectedCoefficient A hd hs hp ho g⁆
  have hMcast : (Int.castRingHom ℚ).mapMatrix M=⁅fieldRoot D ℚ false i,X⁆ := by
    simp only [M,X,Ring.lie_def,map_sub,map_mul,CFSGGeckIntegralMatrices.map_E,
      cast_integerSelectedCoefficient,rational_E_eq,CFSGGeckSerreRepresentation.E]
  have hNcast : (Int.castRingHom ℚ).mapMatrix N=⁅fieldRoot D ℚ true i,Y⁆ := by
    simp only [N,Y,Ring.lie_def,map_sub,map_mul,CFSGGeckIntegralMatrices.map_F,
      cast_integerSelectedCoefficient,rational_F_eq,CFSGGeckSerreRepresentation.F]
  have hcInt : ∃n : ℤ,c=(n:ℚ) := selected_line_scalar_is_integer A hd hs hp ho g M c
    (hMcast.trans hc')
  have hdInt : ∃n : ℤ,d=(n:ℚ) := selected_line_scalar_is_integer A hd hs hp ho k N d
    (hNcast.trans hd'')
  rcases CFSGIntegralPrimitiveLineScalar.integer_inverse_coefficients_are_signs c d hcInt hdInt hprod with h|h
  · refine ⟨1,Or.inl rfl,?_⟩
    simpa only [h,Int.cast_one] using hc'
  · refine ⟨-1,Or.inr rfl,?_⟩
    simpa only [h,Int.cast_neg,Int.cast_one] using hc'

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootBracketUnit
