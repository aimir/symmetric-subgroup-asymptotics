import SymmetricSubgroupAsymptotics.CFSGSymplecticCenterCardinality
import SymmetricSubgroupAsymptotics.CFSGSymplecticElementaryProjectiveCenter
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! In characteristic two the original elementary-to-projective map
is an actual isomorphism, because its already proved scalar centre is
trivial. This does not assert a lifting theorem in odd characteristic. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

def binaryProjectiveEquiv (K : Type) [Field K] [CharP K 2] (r : ℕ) :
    elementaryRootGroup K (r + 1) ≃* elementaryProjective K (r + 1) :=
  MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (r + 1))))
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by
        rw [QuotientGroup.ker_mk', center_eq_bot_of_char_two K r]),
      QuotientGroup.mk'_surjective _⟩

@[simp] theorem binaryProjectiveEquiv_apply (K : Type) [Field K] [CharP K 2]
    (r : ℕ) (g : elementaryRootGroup K (r + 1)) :
    binaryProjectiveEquiv K r g =
      QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (r + 1))) g := rfl

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
