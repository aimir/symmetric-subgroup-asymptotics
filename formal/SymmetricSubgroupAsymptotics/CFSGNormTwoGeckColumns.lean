import SymmetricSubgroupAsymptotics.CFSGNormTwoRootStrings
import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Basic

/-! Actual column transitions for Geck matrices of the norm-two lattice.
The root-string coefficient is proved to be one when addition is possible. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckColumns
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoRootStrings
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    (b : (rootPairing A hs hp).Base)

def negativeIndex (i : Roots A) : Roots A := (rootPairing A hs hp).reflectionPerm i i

theorem negative_val (i : Roots A) : (negativeIndex A hs hp i).val= -i.val := by
  apply castVector_injective
  have he : (rootPairing A hs hp).root (negativeIndex A hs hp i)= -(rootPairing A hs hp).root i := by
    unfold negativeIndex
    rw [RootPairing.root_reflectionPerm,RootPairing.reflection_apply_self]
  simpa only [rootPairing,rootEmbedding,castVector,Pi.neg_apply,Int.cast_neg] using he

theorem E_v_negative (i : b.support) :
    RootPairing.GeckConstruction.e i *ᵥRootPairing.GeckConstruction.v b (negativeIndex A hs hp i)=
      RootPairing.GeckConstruction.u i := by
  change RootPairing.GeckConstruction.e i *ᵥPi.single (Sum.inr (negativeIndex A hs hp i)) 1=_
  rw [Matrix.mulVec_single_one]
  ext (k|k) <;>
    simp [RootPairing.GeckConstruction.e,RootPairing.GeckConstruction.u,
      negativeIndex,RootPairing.indexNeg_neg,(rootPairing A hs hp).ne_zero,Pi.single_apply]

theorem E_v_zero (i : b.support) (j : Roots A)
    (hj : j≠negativeIndex A hs hp i)
    (ha : (rootPairing A hs hp).root i+(rootPairing A hs hp).root j∉
      Set.range (rootPairing A hs hp).root) :
    RootPairing.GeckConstruction.e i *ᵥRootPairing.GeckConstruction.v b j=0 := by
  have hn (k : Roots A) : (rootPairing A hs hp).root k≠
      (rootPairing A hs hp).root i+(rootPairing A hs hp).root j :=
    fun h=>ha ⟨k,h⟩
  have hj' : j≠(rootPairing A hs hp).reflectionPerm i i := hj
  change RootPairing.GeckConstruction.e i *ᵥPi.single (Sum.inr j) 1=0
  rw [Matrix.mulVec_single_one]
  ext (k|k) <;>
    simp [RootPairing.GeckConstruction.e,RootPairing.indexNeg_neg,hj',hn]

theorem E_v_add (i : b.support) (j k : Roots A)
    (hk : (rootPairing A hs hp).root k=
      (rootPairing A hs hp).root i+(rootPairing A hs hp).root j) :
    RootPairing.GeckConstruction.e i *ᵥRootPairing.GeckConstruction.v b j=
      RootPairing.GeckConstruction.v b k := by
  have he := RootPairing.GeckConstruction.e_lie_v_ne (b:=b) hk
  change RootPairing.GeckConstruction.e i *ᵥRootPairing.GeckConstruction.v b j=
    ((rootPairing A hs hp).chainBotCoeff i j+1:ℚ) • RootPairing.GeckConstruction.v b k at he
  rw [chainBotCoeff_of_root_add A hs hp hk] at he
  simpa only [Nat.cast_zero,zero_add,one_smul] using he

theorem E_v_self (i : b.support) :
    RootPairing.GeckConstruction.e i *ᵥRootPairing.GeckConstruction.v b i=0 := by
  apply E_v_zero A hs hp b i i (RootPairing.ne_neg (rootPairing A hs hp) i)
  rintro ⟨k,hk⟩
  have hpair := pairing_of_root_add A hs hp hk
  rw [i.val.property] at hpair
  norm_num at hpair

theorem E_u (i j : b.support) :
    RootPairing.GeckConstruction.e i *ᵥRootPairing.GeckConstruction.u j=
      |b.cartanMatrix i j| • RootPairing.GeckConstruction.v b i :=
  RootPairing.GeckConstruction.e_lie_u i j

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckColumns
