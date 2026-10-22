import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckGram
import Mathlib.Algebra.Lie.SkewAdjoint
import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Relations

/-! The coordinate-base Geck generators preserve their actual height Gram
form. Both root signs use the same integer lattice, including the negative
simple roots; no invariant-form hypothesis is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckCoordinateForm
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoGeckHeightData CFSGNormTwoGeckStepMatrices CFSGNormTwoGeckGram
open CFSGIntegerHeightSign
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)]

theorem rootSign_add_of_root_add (a j k : Roots A)
    (hk : (rootPairing A hs hp).root k=
      (rootPairing A hs hp).root a+(rootPairing A hs hp).root j) :
    rootSign A k=rootSign A a*rootSign A j := by
  have hv : k.val=a.val+j.val := by
    ext t
    have ht := congrFun hk t
    change (k.val t:ℚ)=(a.val t:ℚ)+(j.val t:ℚ) at ht
    exact_mod_cast ht
  change heightSign k.val=heightSign a.val*heightSign j.val
  rw [hv,heightSign_add]

theorem step_skew_of_sign (b : (rootPairing A hs hp).Base)
    (a : Roots A) (i : (b).support) (ha : rootSign A a= -1) :
    (stepMatrix A hs hp b a i).transpose*gram A hs hp b+
      gram A hs hp b*stepMatrix A hs hp b a i=0 := by
  apply step_skew A hs hp b a i ha
  intro j k hk
  rw [rootSign_add_of_root_add A hs hp a j k hk,ha]
  ring

variable (hd : ∀ i,A i i=2) (ho : ∀ i j,i≠j→A i j≤0)
local notation "b" => coordinateBase A hd hs hp ho

theorem E_mem_form (i : (b).support) :
    RootPairing.GeckConstruction.e i∈skewAdjointMatricesLieSubalgebra (gram A hs hp b) := by
  rw [mem_skewAdjointMatricesLieSubalgebra,mem_skewAdjointMatricesSubmodule]
  change (RootPairing.GeckConstruction.e i).transpose*gram A hs hp b=
    gram A hs hp b*(-RootPairing.GeckConstruction.e i)
  rw [mul_neg,eq_neg_iff_add_eq_zero,E_eq_step A hs hp b i]
  exact step_skew_of_sign A hs hp b i i (rootSign_simple A hd hs hp ho i)

theorem F_mem_form (i : (b).support) :
    RootPairing.GeckConstruction.f i∈skewAdjointMatricesLieSubalgebra (gram A hs hp b) := by
  rw [mem_skewAdjointMatricesLieSubalgebra,mem_skewAdjointMatricesSubmodule]
  change (RootPairing.GeckConstruction.f i).transpose*gram A hs hp b=
    gram A hs hp b*(-RootPairing.GeckConstruction.f i)
  rw [mul_neg,eq_neg_iff_add_eq_zero,F_eq_step A hs hp b i]
  apply step_skew_of_sign A hs hp b (negativeIndex A hs hp i) i
  exact (rootSign_negative A hs hp i).trans (rootSign_simple A hd hs hp ho i)

theorem H_mem_form (i : (b).support) :
    RootPairing.GeckConstruction.h i∈skewAdjointMatricesLieSubalgebra (gram A hs hp b) := by
  rw [←RootPairing.GeckConstruction.lie_e_f_same i]
  exact (skewAdjointMatricesLieSubalgebra (gram A hs hp b)).lie_mem
    (E_mem_form A hs hp hd ho i) (F_mem_form A hs hp hd ho i)

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckCoordinateForm
