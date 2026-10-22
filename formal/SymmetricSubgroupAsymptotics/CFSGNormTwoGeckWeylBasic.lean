import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNegativeColumns
import SymmetricSubgroupAsymptotics.CFSGQuadraticWeylStrings
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix

/-! The actual norm-two Geck Weyl operator on its three-dimensional root
block and on all Cartan columns. The remaining root columns are the
one- and two-strings supplied by the same lattice pairing. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylBasic
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoGeckNegativeColumns CFSGQuadraticWeylStrings
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    (b : (rootPairing A hs hp).Base)

def eOperator (i : b.support) : Module.End ℚ (b.support⊕Roots A→ℚ) :=
  Matrix.toLinAlgEquiv' (RootPairing.GeckConstruction.e i)

def fOperator (i : b.support) : Module.End ℚ (b.support⊕Roots A→ℚ) :=
  Matrix.toLinAlgEquiv' (RootPairing.GeckConstruction.f i)

def weylOperator (i : b.support) : Module.End ℚ (b.support⊕Roots A→ℚ) :=
  word (eOperator A hs hp b i) (fOperator A hs hp b i)

theorem E_u_self (i : b.support) :
    eOperator A hs hp b i (RootPairing.GeckConstruction.u i)=
      (2:ℚ) • RootPairing.GeckConstruction.v b i := by
  change RootPairing.GeckConstruction.e i*ᵥRootPairing.GeckConstruction.u i=_
  simpa [RootPairing.Base.cartanMatrix_apply_same,two_smul] using E_u A hs hp b i i

theorem F_u_self (i : b.support) :
    fOperator A hs hp b i (RootPairing.GeckConstruction.u i)=
      (2:ℚ) • RootPairing.GeckConstruction.v b (negativeIndex A hs hp i) := by
  change RootPairing.GeckConstruction.f i*ᵥRootPairing.GeckConstruction.u i=_
  simpa [RootPairing.Base.cartanMatrix_apply_same,two_smul] using F_u A hs hp b i i

theorem weyl_on_triple (i : b.support) :
    weylOperator A hs hp b i (RootPairing.GeckConstruction.u i)= -RootPairing.GeckConstruction.u i ∧
    weylOperator A hs hp b i (RootPairing.GeckConstruction.v b i)=
      RootPairing.GeckConstruction.v b (negativeIndex A hs hp i) ∧
    weylOperator A hs hp b i (RootPairing.GeckConstruction.v b (negativeIndex A hs hp i))=
      RootPairing.GeckConstruction.v b i := by
  exact word_triple (eOperator A hs hp b i) (fOperator A hs hp b i)
    (RootPairing.GeckConstruction.u i) (RootPairing.GeckConstruction.v b i)
    (RootPairing.GeckConstruction.v b (negativeIndex A hs hp i))
    (E_u_self A hs hp b i) (E_v_self A hs hp b i) (E_v_negative A hs hp b i)
    (F_u_self A hs hp b i) (F_v_self A hs hp b i) (F_v_negative A hs hp b i)

theorem weyl_on_cartan (i j : b.support) :
    weylOperator A hs hp b i (RootPairing.GeckConstruction.u j)=
      RootPairing.GeckConstruction.u j-
        (((|b.cartanMatrix i j|:ℤ):ℚ)) • RootPairing.GeckConstruction.u i := by
  apply word_cartan (eOperator A hs hp b i) (fOperator A hs hp b i)
    (RootPairing.GeckConstruction.u i) (RootPairing.GeckConstruction.v b i)
    (RootPairing.GeckConstruction.v b (negativeIndex A hs hp i))
    (RootPairing.GeckConstruction.u j) (((|b.cartanMatrix i j|:ℤ):ℚ))
  · exact E_u_self A hs hp b i
  · exact E_v_self A hs hp b i
  · exact E_v_negative A hs hp b i
  · exact F_u_self A hs hp b i
  · exact F_v_self A hs hp b i
  · exact F_v_negative A hs hp b i
  · simpa only [Int.cast_smul_eq_zsmul] using E_u A hs hp b i j
  · simpa only [Int.cast_smul_eq_zsmul] using F_u A hs hp b i j

theorem weyl_four_cartan (i j : b.support) :
    ((weylOperator A hs hp b i)^4) (RootPairing.GeckConstruction.u j)=
      RootPairing.GeckConstruction.u j := by
  have hu := (weyl_on_triple A hs hp b i).1
  have hv := weyl_on_cartan A hs hp b i j
  have htwo : ((weylOperator A hs hp b i)^2) (RootPairing.GeckConstruction.u j)=
      RootPairing.GeckConstruction.u j := by
    simp only [pow_two,Module.End.mul_apply,hv,map_sub,map_smul,hu]
    module
  rw [show 4=2+2 by rfl,pow_add,Module.End.mul_apply,htwo,htwo]

theorem weyl_four_positive (i : b.support) :
    ((weylOperator A hs hp b i)^4) (RootPairing.GeckConstruction.v b i)=
      RootPairing.GeckConstruction.v b i := by
  have hpos := (weyl_on_triple A hs hp b i).2.1
  have hneg := (weyl_on_triple A hs hp b i).2.2
  simp only [pow_succ,pow_zero,Module.End.mul_apply,Module.End.one_apply,hpos,hneg]

theorem weyl_four_negative (i : b.support) :
    ((weylOperator A hs hp b i)^4) (RootPairing.GeckConstruction.v b (negativeIndex A hs hp i))=
      RootPairing.GeckConstruction.v b (negativeIndex A hs hp i) := by
  have hpos := (weyl_on_triple A hs hp b i).2.1
  have hneg := (weyl_on_triple A hs hp b i).2.2
  simp only [pow_succ,pow_zero,Module.End.mul_apply,Module.End.one_apply,hpos,hneg]

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylBasic
