import SymmetricSubgroupAsymptotics.CFSGOrthogonalDMatrixScalarExtension
import SymmetricSubgroupAsymptotics.CFSGCenterQuotientEquiv

/-! Literal D elementary root subgroups and their FULL-centre quotients
are functorial under an actual coefficient-field equivalence. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDElementaryFieldEquivalence
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDMatrixScalarExtension
variable {F K : Type} [Field F] [Field K]

theorem scalar_inverse (e : F≃+*K) (r : ℕ) (g : elementaryRootGroup F r) :
    scalarElementaryHom e.symm.toRingHom r (scalarElementaryHom e.toRingHom r g)=g := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  change e.symm (e ((g.val : Mat F r) i j))=(g.val : Mat F r) i j
  exact e.symm_apply_apply _

def elementaryEquiv (e : F≃+*K) (r : ℕ) :
    elementaryRootGroup F r≃*elementaryRootGroup K r :=
  MulEquiv.ofBijective (scalarElementaryHom e.toRingHom r)
    ⟨(show Function.LeftInverse (scalarElementaryHom e.symm.toRingHom r)
        (scalarElementaryHom e.toRingHom r) from scalar_inverse e r).injective,
      fun h=>⟨scalarElementaryHom e.symm.toRingHom r h,scalar_inverse e.symm r h⟩⟩

def projectiveEquiv (e : F≃+*K) (r : ℕ) :
    elementaryProjective F r≃*elementaryProjective K r :=
  CFSGCenterQuotientEquiv.equiv (elementaryEquiv e r)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDElementaryFieldEquivalence
