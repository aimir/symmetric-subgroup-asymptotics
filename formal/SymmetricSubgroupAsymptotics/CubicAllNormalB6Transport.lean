import SymmetricSubgroupAsymptotics.CubicAllNormalB6Envelope
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixPairCharacterOnlySource

/-! Retain the original degree-twelve action while importing a proved
structural kernel chart through an exact group equivalence. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
namespace CubicAllNormalB6Transport

variable {U G : Type} [Group U] [Finite U] [Group G] [Finite G]
  (f : U ≃* G) (top : G →* CyclicThree)
  (A : Rep (ZMod 2) CyclicThree) (E : OriginalKernelModuleChart top A)

def originalTop : U →* CyclicThree := top.comp f.toMonoidHom

def kernelEquiv : (originalTop f top).ker ≃* top.ker where
  toFun p := ⟨f p,p.2⟩
  invFun p := ⟨f.symm p,by
    change top (f (f.symm (p : G))) = 1
    rw [f.apply_symm_apply]
    exact MonoidHom.mem_ker.mp p.2⟩
  left_inv p := by apply Subtype.ext; exact f.symm_apply_apply p
  right_inv p := by apply Subtype.ext; exact f.apply_symm_apply p
  map_mul' p q := by apply Subtype.ext; exact f.map_mul p q

/-- The original actual kernel, with its original conjugation identity. -/
def originalChart : OriginalKernelModuleChart (originalTop f top) A where
  equiv := E.equiv.trans (kernelEquiv f top).symm
  conjugate q a := by
    apply f.injective
    change f (f.symm (E.equiv (Multiplicative.ofAdd (A.ρ (top (f q)) a)) : G)) =
      f (q * f.symm (E.equiv (Multiplicative.ofAdd a) : G) * q⁻¹)
    simp only [map_mul,map_inv,f.apply_symm_apply]
    exact E.conjugate (f q) a

/-- A full B6 action certificate for the literal original twelve-point
subgroup, using every actual normal quotient rather than a registry census. -/
def originalActionCertificate
    {H : Subgroup (Equiv.Perm (Fin 12))}
    (f : H ≃* G) (htop : Function.Surjective top)
    (D : CubicBinaryCoordinates A.ρ)
    (hscalar : ∃ j : Fin 2, ∃ p : top.ker,
      CubicElementaryKernelCoordinates.scalar top A.ρ E.equiv.symm D j p ≠ 1)
    (hKP : KovacsPraegerAbelianizationBound) (F : BinaryPairFrame H (Fin 6)) :
    Non2UnipotentPrefixFiniteMenu.PreE7B6ActionCertificate H := by
  let t := originalTop f top
  let C := originalChart f top A E
  have ht : Function.Surjective t := htop.comp f.surjective
  have hs : ∃ j : Fin 2, ∃ p : t.ker,
      CubicElementaryKernelCoordinates.scalar t A.ρ C.equiv.symm D j p ≠ 1 := by
    obtain ⟨j,p,hp⟩ := hscalar
    refine ⟨j,(kernelEquiv f top).symm p,?_⟩
    simpa [C,originalChart,CubicElementaryKernelCoordinates.scalar] using hp
  exact
    { blockChart := Non2UnipotentPrefixFiniteMenu.sixPairBlockChart F
      preserves := Non2UnipotentPrefixFiniteMenu.sixPairBlockChart_preserves F
      quotient := fun N => CubicAllNormalB6Envelope.quotientCertificate t ht A C D hs hKP N.1 }

end CubicAllNormalB6Transport
end SymmetricSubgroupAsymptotics
end
