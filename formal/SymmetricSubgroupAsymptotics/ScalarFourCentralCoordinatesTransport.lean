import SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates

/-! Actual group isomorphisms transport the complete central-repeat
structure, including its exact kernels and conjugation actions. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
variable {Q H T : Type} [Group Q] [Group H] [Group T] {c d : ℕ}
  (D : ScalarFourCentralTopCoordinates Q T c d) (e : H ≃* Q)

private def topKernelEquiv : (D.top.comp e.toMonoidHom).ker ≃* D.top.ker where
  toFun z := ⟨e (z : H),z.property⟩
  invFun z := ⟨e.symm (z : Q),by
    change D.top (e (e.symm (z : Q)))=1
    rw [e.apply_symm_apply]
    exact z.property⟩
  left_inv z := Subtype.ext (e.symm_apply_apply z)
  right_inv z := Subtype.ext (e.apply_symm_apply z)
  map_mul' z w := Subtype.ext (e.map_mul z w)

private def transportedActive : (D.top.comp e.toMonoidHom).ker →* (Fin d → ScalarFour) :=
  D.active.comp (topKernelEquiv D e).toMonoidHom

private def centralKernelEquiv : (transportedActive D e).ker ≃* D.active.ker where
  toFun z := ⟨topKernelEquiv D e z,z.property⟩
  invFun z := ⟨(topKernelEquiv D e).symm z,by
    change D.active (topKernelEquiv D e ((topKernelEquiv D e).symm z))=1
    rw [MulEquiv.apply_symm_apply]
    exact z.property⟩
  left_inv z := by apply Subtype.ext; exact (topKernelEquiv D e).symm_apply_apply _
  right_inv z := by apply Subtype.ext; exact (topKernelEquiv D e).apply_symm_apply _
  map_mul' z w := by apply Subtype.ext; exact map_mul _ _ _

def transport : ScalarFourCentralTopCoordinates H T c d where
  top := D.top.comp e.toMonoidHom
  top_surjective := D.top_surjective.comp e.surjective
  cubic := D.cubic
  active := transportedActive D e
  central z h := by
    apply e.injective
    rw [map_mul,map_mul]
    exact D.central (centralKernelEquiv D e z) (e h)
  centralCoordinates := D.centralCoordinates.comp (centralKernelEquiv D e).toMonoidHom
  centralCoordinates_injective := D.centralCoordinates_injective.comp
    (centralKernelEquiv D e).injective
  cubic_action n hn k j := by
    have he : topKernelEquiv D e (MulAut.conjNormal n k)=
        MulAut.conjNormal (e n) (topKernelEquiv D e k) := by
      apply Subtype.ext
      change e (n*(k : H)*n⁻¹)=e n*e (k : H)*(e n)⁻¹
      rw [map_mul,map_mul,map_inv]
    change D.active (topKernelEquiv D e (MulAut.conjNormal n k)) j=
      scalarFourTwist 1 (D.active (topKernelEquiv D e k) j)
    rw [he]
    exact D.cubic_action (e n) hn (topKernelEquiv D e k) j

end SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
