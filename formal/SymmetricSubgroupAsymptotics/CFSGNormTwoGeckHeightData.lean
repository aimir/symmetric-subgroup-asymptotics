import SymmetricSubgroupAsymptotics.CFSGIntegerHeightSign
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckColumns
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateBase

/-! Every sign condition needed by the actual Geck Gram matrix is derived
from the coordinate height of the same original norm-two integer roots. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckHeightData
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGIntegerHeightSign
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hd : ∀ i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]

def rootSign (i : Roots A) : ℚ := heightSign i.val

def negativePerm : Equiv.Perm (Roots A) :=
  Function.Involutive.toPerm (negativeIndex A hs hp) (by
    intro i
    apply Subtype.ext
    rw [negative_val,negative_val,neg_neg])

theorem rootSign_negative (i : Roots A) : rootSign A (negativePerm A hs hp i)=rootSign A i := by
  change heightSign (negativeIndex A hs hp i).val=heightSign i.val
  rw [negative_val,heightSign_neg]

theorem rootSign_ne_zero (i : Roots A) : rootSign A i≠0 := heightSign_ne_zero i.val

theorem rootSign_simple (i : (coordinateBase A hd hs hp ho).support) : rootSign A i= -1 := by
  have hi : (i:Roots A)∈coordinateSupport A hd := i.property
  change (i:Roots A)∈(coordinateSupport A hd:Set (Roots A)) at hi
  rw [coordinateSupport_coe] at hi
  obtain ⟨j,hj⟩ := hi
  rw [←hj]
  exact heightSign_single j

theorem rootSign_shift (i : (coordinateBase A hd hs hp ho).support) (j k : Roots A)
    (hk : (rootPairing A hs hp).root k=
      (rootPairing A hs hp).root i+(rootPairing A hs hp).root j) :
    rootSign A k= -rootSign A j := by
  have hv : k.val=(i:Roots A).val+j.val := by
    ext t
    have ht := congrFun hk t
    change (k.val t:ℚ)=((i:Roots A).val t:ℚ)+(j.val t:ℚ) at ht
    exact_mod_cast ht
  have hi := rootSign_simple A hd hs hp ho i
  change heightSign (i:Roots A).val= -1 at hi
  change heightSign k.val= -heightSign j.val
  rw [hv,heightSign_add,hi]
  ring

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckHeightData
