import SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates

/-! Relabel the retained actual finite top through an explicit group
isomorphism. Original target, active kernel, and central kernel are kept. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
variable {Q T S : Type} [Group Q] [Group T] [Group S] {c d : ℕ}
  (D : ScalarFourCentralTopCoordinates Q T c d) (e : T ≃* S)

private def equivKernel : (e.toMonoidHom.comp D.top).ker ≃* D.top.ker where
  toFun k := ⟨k.val,e.injective (k.property.trans e.map_one.symm)⟩
  invFun k := ⟨k.val,by change e (D.top k.val)=1; rw [k.property,e.map_one]⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private def equivActiveKernel : (D.active.comp (equivKernel D e).toMonoidHom).ker ≃*
    D.active.ker where
  toFun z := ⟨equivKernel D e z.val,z.property⟩
  invFun z := ⟨(equivKernel D e).symm z.val,by
    change D.active (equivKernel D e ((equivKernel D e).symm z.val))=1
    rw [MulEquiv.apply_symm_apply]
    exact z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

def topEquiv : ScalarFourCentralTopCoordinates Q S c d where
  top := e.toMonoidHom.comp D.top
  top_surjective := e.surjective.comp D.top_surjective
  cubic := e D.cubic
  active := D.active.comp (equivKernel D e).toMonoidHom
  central := by intro z g; exact D.central (equivActiveKernel D e z) g
  centralCoordinates := D.centralCoordinates.comp (equivActiveKernel D e).toMonoidHom
  centralCoordinates_injective := D.centralCoordinates_injective.comp (equivActiveKernel D e).injective
  cubic_action := by
    intro v hv k j
    have hv' : D.top v=D.cubic := e.injective hv
    exact D.cubic_action v hv' (equivKernel D e k) j

end SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
