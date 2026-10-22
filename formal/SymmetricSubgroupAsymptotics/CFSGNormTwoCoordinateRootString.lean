import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNonrootDegreeZero
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckCartanDegreeAction
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRationalWeylCollecting
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixLieDegree
import SymmetricSubgroupAsymptotics.CFSGIntegerNegativeSimpleStep
import SymmetricSubgroupAsymptotics.CFSGSlTwoUnitString

/-! The actual rational length-one string through a positive original
root. Norm-six degree vanishing and the original Cartan diagonal prove
the lowering relation and Jacobi identity; neither is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootString
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoGeckNegativeLatticeDegree CFSGNormTwoGeckRationalAdjointStrings
open CFSGNormTwoGeckRationalWeylCollecting CFSGNormTwoGeckCartanDegreeAction
open CFSGGradedMatrixSupport CFSGGradedMatrixLieDegree
open CFSGIntegerNegativeSimpleStep CFSGSlTwoUnitString
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀
private abbrev CoordMat := Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) ℚ
local notation "Mat" => CoordMat A hd hs hp ho
local notation "ell" => latticeWeight A hs hp b₀

theorem lower_root_bracket_zero (k : Roots A) (hk : ∀t,0≤k.val t) (i : Fin r)
    (hpair : integerPairing A k.val (s₀ i:Roots A).val= -1)
    (M : Mat) (hM : M∈RootPairing.GeckConstruction.lieAlgebra b₀)
    (hdeg : Supported ell (fun v=>v+k.val) M) : ⁅fieldRoot D ℚ true i,M⁆=0 := by
  let a : Fin r→ℤ := Pi.single i (1:ℤ)
  change integerPairing A k.val a= -1 at hpair
  have ha : integerPairing A a a=2 := by
    change A.toBilin' (Pi.single i (1:ℤ)) (Pi.single i (1:ℤ))=2
    rw [Matrix.toBilin'_single,hd]
  have hnorm : integerPairing A (k.val-a) (k.val-a)=6 := by
    simp only [map_sub,LinearMap.sub_apply]
    rw [k.property,hpair,integer_symmetric A hs a k.val,hpair,ha]
    norm_num
  have hFmem : fieldRoot D ℚ true i∈RootPairing.GeckConstruction.lieAlgebra b₀ := by
    rw [rational_F_eq]
    exact RootPairing.GeckConstruction.f_mem_lieAlgebra (s₀ i)
  have hFdeg : Supported ell (fun v=>v+ -a) (fieldRoot D ℚ true i) := by
    rw [rational_F_eq]
    simpa only [sub_eq_add_neg] using rational_F_lattice_support A hs hp b₀ (s₀ i)
  have hNmem := (RootPairing.GeckConstruction.lieAlgebra b₀).lie_mem hFmem hM
  have hNdeg : Supported ell (fun v=>v+(k.val-a)) ⁅fieldRoot D ℚ true i,M⁆ := by
    apply supported_congr (supported_lie ell (-a) k.val _ _ hFdeg hdeg)
    intro v
    abel
  rcases sub_simple_nonnegative_or_mixed (integerPairing A) k.val hk i ha
      (by change integerPairing A k.val a<0;omega) with hn|hn
  · exact CFSGNormTwoCoordinateNonrootDegreeZero.nonnegative_norm_four_or_six_degree_zero
      A hd hs hp ho _ (k.val-a) hNmem hNdeg hn (Or.inr hnorm)
  · obtain ⟨t,u,ht,hu⟩ := hn
    exact CFSGNormTwoCoordinateGeneratedMixedDegree.mixed_degree_zero
      A hd hs hp ho _ (k.val-a) hNmem hNdeg t u ht hu

theorem root_lowering_after_raising (k : Roots A) (hk : ∀t,0≤k.val t) (i : Fin r)
    (hpair : integerPairing A k.val (s₀ i:Roots A).val= -1)
    (M : Mat) (hM : M∈RootPairing.GeckConstruction.lieAlgebra b₀)
    (hdeg : Supported ell (fun v=>v+k.val) M) :
    ⁅fieldRoot D ℚ true i,⁅fieldRoot D ℚ false i,M⁆⁆=M := by
  have hEF : ⁅fieldRoot D ℚ false i,fieldRoot D ℚ true i⁆=
      RootPairing.GeckConstruction.h (s₀ i) := by
    rw [rational_E_eq,rational_F_eq]
    exact (RootPairing.GeckConstruction.isSl2Triple (s₀ i)).lie_e_f
  have hHX : ⁅RootPairing.GeckConstruction.h (s₀ i),M⁆= -M := by
    have hh := cartan_lie_of_lattice_degree A hs hp b₀ (s₀ i) k.val M hdeg
    rw [hpair] at hh
    simpa only [Int.cast_neg,Int.cast_one,neg_one_smul] using hh
  exact lowering_after_raising _ _ _ M hEF hHX
    (lower_root_bracket_zero A hd hs hp ho k hk i hpair M hM hdeg)

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootString
