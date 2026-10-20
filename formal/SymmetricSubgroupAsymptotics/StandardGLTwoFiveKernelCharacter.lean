import SymmetricSubgroupAsymptotics.StandardGLTwoFiveProjective
import Mathlib.RingTheory.IntegralDomain
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! The actual scalar kernel has a faithful C4 character. The cyclic
coordinate is derived from finite-field units, not supplied as data. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.StandardGLTwoFiveProjective

/-- Finite field units are cyclic; their already proved order is four. -/
def unitsCyclicFourEquiv : (ZMod 5)ˣ ≃* Multiplicative (ZMod 4) := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  let hex := IsCyclic.exists_generator (α := (ZMod 5)ˣ)
  exact (zmodMulEquivOfGenerator (Classical.choose_spec hex) card_units_five).symm

def projectiveKernelCyclicFourEquiv (h : PublishedProjectiveIsomorphism) :
    (projective h).ker ≃* Multiplicative (ZMod 4) :=
  (scalarKernelEquiv h).symm.trans unitsCyclicFourEquiv

def kernelCharacter (h : PublishedProjectiveIsomorphism) :
    (projective h).ker →* Multiplicative (ZMod 4) :=
  (projectiveKernelCyclicFourEquiv h).toMonoidHom

theorem kernelCharacter_injective (h : PublishedProjectiveIsomorphism) :
    Function.Injective (kernelCharacter h) :=
  (projectiveKernelCyclicFourEquiv h).injective

theorem projective_kernel_cyclic (h : PublishedProjectiveIsomorphism) :
    IsCyclic (projective h).ker :=
  isCyclic_of_injective (kernelCharacter h) (kernelCharacter_injective h)

end SymmetricSubgroupAsymptotics.StandardGLTwoFiveProjective
