import SymmetricSubgroupAsymptotics.ProductBlockFramePointTransport
import SymmetricSubgroupAsymptotics.ProductBlockFrameOriginalBlocks
import Mathlib.GroupTheory.PGroup

/-! Actual point transport preserves binary block kernels and properness
of the chosen physical block stabilizer. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ProductBlockFrame
variable {X Y I F : Type} {U : Subgroup (Equiv.Perm X)}
    {V : Subgroup (Equiv.Perm Y)}
    (C : ProductBlockFrame U I F) (e : U ≃* V) (points : X ≃ Y)
    (he : ∀ (u : U) (x : X),
      points ((u : Equiv.Perm X) x) = (e u : Equiv.Perm Y) (points x))
local notation "D" => ofPointEquiv C e points he

theorem ofPointEquiv_kernel_binary (hK : IsPGroup 2 C.top.ker) :
    IsPGroup 2 (ofPointEquiv C e points he).top.ker := by
  let f : (ofPointEquiv C e points he).top.ker →* C.top.ker := {
    toFun := fun u => ⟨e.symm u.1,u.2⟩
    map_one' := by apply Subtype.ext; exact map_one e.symm
    map_mul' := by intro u v; apply Subtype.ext; exact map_mul e.symm u.1 v.1 }
  apply hK.of_injective f
  intro u v heq
  apply Subtype.ext
  apply e.symm.injective
  exact congrArg Subtype.val heq

theorem ofPointEquiv_stabilizer_proper (i : I) :
    letI : MulAction U I := C.topMulAction
    letI : MulAction V I := (ofPointEquiv C e points he).topMulAction
    (MulAction.stabilizer U i < ⊤) → MulAction.stabilizer V i < ⊤ := by
  letI : MulAction U I := C.topMulAction
  letI : MulAction V I := (ofPointEquiv C e points he).topMulAction
  intro hproper
  obtain ⟨g,_,hg⟩ := SetLike.exists_of_lt hproper
  apply lt_of_le_of_ne le_top
  intro htop
  have hm : e g ∈ MulAction.stabilizer V i := by
    rw [htop]
    exact Subgroup.mem_top _
  apply hg
  change C.top g i = i
  change (ofPointEquiv C e points he).top (e g) i = i at hm
  simpa only [ofPointEquiv,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
    e.symm_apply_apply] using hm

end SymmetricSubgroupAsymptotics.ProductBlockFrame
end
