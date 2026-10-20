import SymmetricSubgroupAsymptotics.BinaryFourSymmetricBlockPermutation

/-! The literal zero-core S4 block chart. Translation offsets are retained
in the source elements; no splitting of the original action is assumed. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryFourSymmetricBlockActions

open BinaryFourBlockAugmentation BinaryFourFullBlockCoordinates SemidirectProduct

def symmetricGauge (b : Fin 4) : Local ≃ₗ[Scalar] Local :=
  ![1, localReflection, localCycle⁻¹, localCycle] b

def symmetricPointEquiv : (Fin 4 × Local) ≃ Fin 16 where
  toFun x := Fin.ofNat 16 (4 * x.1.val + binaryVectorMask (symmetricGauge x.1 x.2))
  invFun i :=
    let b : Fin 4 := ⟨i.val / 4, by omega⟩
    (b, (symmetricGauge b).symm (localOfMask (i.val % 4)))
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalRelabel : Equiv.Perm (Fin 16) := pointEquiv.symm.trans symmetricPointEquiv

def literalPermutation : SymmetricAmbient →* Equiv.Perm (Fin 16) :=
  literalRelabel.permCongrHom.toMonoidHom.comp symmetricPermutation

/-- Reflection, three-cycle, the two Klein generators, then the identity. -/
def literalComplement (i : Fin 5) : SymmetricComplement :=
  ![inr (Multiplicative.ofAdd (1 : ZMod 2)),
    inl cElement, inl vElement, inl uElement, 1] i

def literalLift (x : FullCoordinates) (i : Fin 5) : SymmetricAmbient :=
  inl (Multiplicative.ofAdd x) * inr (literalComplement i)

end BinaryFourSymmetricBlockActions
end SymmetricSubgroupAsymptotics

end
