import SymmetricSubgroupAsymptotics.BinaryElementaryPairMonomialWidth
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Image

/-! Abstract relabeling of the finite leading-support poset. This
relabels neither original point coordinates nor original module vectors. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryBooleanFourSupportRelabel
open BinaryElementaryPairMonomialWidth

def supportEquiv : Fin 16 ≃ Finset (Fin 4) :=
  Equiv.ofBijective support (by decide)

def mask (p : Equiv.Perm (Fin 4)) : Equiv.Perm (Fin 16) :=
  supportEquiv.trans (p.finsetCongr.trans supportEquiv.symm)

theorem support_mask (p : Equiv.Perm (Fin 4)) (a : Fin 16) :
    support (mask p a) = (support a).map p.toEmbedding := by
  change supportEquiv (supportEquiv.symm (p.finsetCongr (support a))) = _
  rw [Equiv.apply_symm_apply, Equiv.finsetCongr_apply]

def monomial (p : Equiv.Perm (Fin 4)) : Equiv.Perm Monomial :=
  Equiv.prodCongr (Equiv.refl Bool) (mask p)

@[simp] theorem monomial_apply (p : Equiv.Perm (Fin 4)) (l : Bool) (a : Fin 16) :
    monomial p (l, a) = (l, mask p a) := rfl

end SymmetricSubgroupAsymptotics.BinaryBooleanFourSupportRelabel
