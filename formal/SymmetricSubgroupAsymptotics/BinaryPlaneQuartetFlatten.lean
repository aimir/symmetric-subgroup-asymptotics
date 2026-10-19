import SymmetricSubgroupAsymptotics.BinaryTwistedQuartetActualUniform
import SymmetricSubgroupAsymptotics.BinaryPlanePermutationAffineEquiv

/-! A literal binary eight-coordinate chart for four actual planes. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPlaneQuartetFlatten
open BinaryPlanePermutationAffineEquiv
abbrev Vector := Fin 8 → ZMod 2

def flat : (Fin 4 → Plane) ≃ₗ[ZMod 2] Vector where
  toFun v i := v ⟨i.val/2,by omega⟩ ⟨i.val%2,by omega⟩
  invFun v i j := v ⟨2*i.val+j.val,by omega⟩
  left_inv v := by
    funext i j
    change v ⟨(2*i.val+j.val)/2,by omega⟩ ⟨(2*i.val+j.val)%2,by omega⟩=v i j
    have hi : (⟨(2*i.val+j.val)/2,by omega⟩ : Fin 4)=i := by
      apply Fin.ext
      change (2*i.val+j.val)/2=i.val
      omega
    have hj : (⟨(2*i.val+j.val)%2,by omega⟩ : Fin 2)=j := by
      apply Fin.ext
      change (2*i.val+j.val)%2=j.val
      omega
    rw [hi,hj]
  right_inv v := by
    funext i
    change v ⟨2*(i.val/2)+i.val%2,by omega⟩=v i
    congr 1
    apply Fin.ext
    change 2*(i.val/2)+i.val%2=i.val
    omega
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end SymmetricSubgroupAsymptotics.BinaryPlaneQuartetFlatten
