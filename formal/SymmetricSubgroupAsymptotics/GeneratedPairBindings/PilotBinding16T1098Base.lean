import SymmetricSubgroupAsymptotics.BinaryPairSchreierBinding
import SymmetricSubgroupAsymptotics.BinaryPairFrameGenerators
import SymmetricSubgroupAsymptotics.BinaryGeneratorWords
import SymmetricSubgroupAsymptotics.GeneratedKernelAxes.Pilot077
import SymmetricSubgroupAsymptotics.GeneratedAction16.Data


/-! Exact original action, original generator top and correlated flip
kernel for 16T1098. All point and basis witnesses are checked by Lean. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairBinding16T1098
abbrev Original := Subgroup.closure (Set.range BinaryActionData16.node1098Generators)
abbrev SourceTop := FiniteGroupRow 16
local instance pilotBaseGroup : Group SourceTop := BinaryTopSource046.group

def generators (j : Fin 5) : Original := ⟨BinaryActionData16.node1098Generators j,Subgroup.subset_closure ⟨j,rfl⟩⟩
theorem generators_full : Subgroup.closure (Set.range generators)=⊤ :=
  binaryNormal_full_generators_of_equiv BinaryActionData16.node1098Generators generators (MulEquiv.refl _) (fun _ => rfl)

def originalWord (ws : List (Fin 5)) : Original :=
  ⟨(ws.map BinaryActionData16.node1098Generators).prod,Subgroup.list_prod_mem _ (by
    intro x hx
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hx
    exact Subgroup.subset_closure ⟨j,rfl⟩)⟩

def frame : Fin 8 × ZMod 2 ≃ Fin 16 where
  toFun p := (#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] : Array (Fin 16))[2*p.1.val+p.2.val]!
  invFun x := ((#[0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7] : Array (Fin 8))[x.val]!,
    (#[0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1] : Array (ZMod 2))[x.val]!)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def top0 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def top1 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,2,3,4,5,6,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def top2 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,3,0,1,6,7,4,5] : Array (Fin 8))[x.val]!
  invFun x := (#[2,3,0,1,6,7,4,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def top3 : Equiv.Perm (Fin 8) where
  toFun x := (#[3,2,1,0,4,5,6,7] : Array (Fin 8))[x.val]!
  invFun x := (#[3,2,1,0,4,5,6,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def top4 : Equiv.Perm (Fin 8) where
  toFun x := (#[6,5,4,7,1,2,3,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,4,5,6,2,1,0,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def tops (j : Fin 5) : Equiv.Perm (Fin 8) := (if j.val < 2 then (if j.val < 1 then top0 else top1) else (if j.val < 3 then top2 else (if j.val < 4 then top3 else top4)))
theorem preserves : ∀ j, BinaryPairFrame.Preserves frame (BinaryActionData16.node1098Generators j) (tops j) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel

def physicalFrame : BinaryPairFrame Original (Fin 8) :=
  BinaryPairFrame.ofGenerators frame BinaryActionData16.node1098Generators tops preserves

end SymmetricSubgroupAsymptotics.BinaryPairBinding16T1098
