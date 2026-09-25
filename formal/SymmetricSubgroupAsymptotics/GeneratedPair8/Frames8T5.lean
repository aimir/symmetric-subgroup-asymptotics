import SymmetricSubgroupAsymptotics.BinaryPairFrames
import SymmetricSubgroupAsymptotics.FiniteCayleyMaps
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T5

/-! Shared actual physical pair frames for 8T5. Generated from the
original frame and original source permutations. Kernel checks bind all
point actions; BinaryPairFrame proves the reversible actual flip chart. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPair8T5
abbrev Source := FiniteGroupRow 8
local instance : Group Source := BinaryMenuCayley8T5.group

namespace Frame0
def frame : Fin 4 × ZMod 2 ≃ Fin 8 where
  toFun p := (#[0,2,1,7,3,5,4,6] : Array (Fin 8))[2*p.1.val+p.2.val]!
  invFun x := ((#[0,1,0,2,3,2,3,1] : Array (Fin 4))[x.val]!,
    (#[0,0,1,0,0,1,1,1] : Array (ZMod 2))[x.val]!)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def top0 : Equiv.Perm (Fin 4) where
  toFun x := (#[3,2,1,0] : Array (Fin 4))[x.val]!
  invFun x := (#[3,2,1,0] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def top1 : Equiv.Perm (Fin 4) where
  toFun x := (#[2,3,0,1] : Array (Fin 4))[x.val]!
  invFun x := (#[2,3,0,1] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def top2 : Equiv.Perm (Fin 4) where
  toFun x := (#[1,0,3,2] : Array (Fin 4))[x.val]!
  invFun x := (#[1,0,3,2] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def top3 : Equiv.Perm (Fin 4) where
  toFun x := (#[0,1,2,3] : Array (Fin 4))[x.val]!
  invFun x := (#[0,1,2,3] : Array (Fin 4))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def values (i : Fin 8) : Equiv.Perm (Fin 4) :=
  (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then top2 else top3) else (if i.val < 3 then top2 else top0)) else (if i.val < 6 then (if i.val < 5 then top1 else top0) else (if i.val < 7 then top1 else top3)))
private def images (j : Fin 2) : Equiv.Perm (Fin 4) :=
  (if j.val < 1 then top2 else top0)
private theorem step_checked : ∀ i j,
    values (BinaryMenuCayley8T5.certificate.next i j)=values i*images j := (by decide +kernel)
private theorem identity_checked : values BinaryMenuCayley8T5.certificate.identity=1 := by decide +kernel

def topHom : Source →* Equiv.Perm (Fin 4) where
  toFun u := values u.index
  map_one' := identity_checked
  map_mul' u v := by
    change values (BinaryMenuCayley8T5.certificate.walk u.index
      (BinaryMenuCayley8T5.certificate.words v.index))=values u.index*values v.index
    rw [EncodedCayleyCertificate.values_walk _ values images step_checked,
      ← EncodedCayleyCertificate.values_word _ values images step_checked identity_checked]

private theorem frame_checked : ∀ i : Fin 8, ∀ p : Fin 4 × ZMod 2,
    (frame.symm (finFunctionFinEquiv.symm (BinaryMenuCayley8T5.certificate.rows i) (frame p))).1=
      values i p.1 := (by decide +kernel)

/-- The exact original source, its exact pair action, and all original points. -/
def physicalFrame : BinaryPairFrame
    (Subgroup.closure (Set.range BinaryMenuCayley8T5.generators)) (Fin 4) :=
  BinaryPairFrame.ofEquiv BinaryMenuCayley8T5.originalEquiv topHom frame (by
    intro u p
    change (frame.symm (BinaryMenuCayley8T5.certificate.toCayley.elements u.index (frame p))).1=
      values u.index p.1
    rw [binaryPair_source_row_apply]
    exact frame_checked u.index p)

/-- The canonical binary chart retains the literal physical kernel. -/
def kernelChart : physicalFrame.top.ker ≃* Multiplicative physicalFrame.kernelSpace :=
  physicalFrame.kernelChart

end Frame0

end SymmetricSubgroupAsymptotics.BinaryPair8T5
