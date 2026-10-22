import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexCenter
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! In odd characteristic the SAME natural elementary B group has
trivial centre, so its original full-centre quotient map is an actual
isomorphism. This is not an assumed automorphism-lifting principle. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices

def oddProjectiveEquiv (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (r : ℕ) :
    elementaryRootGroup K (r + 1) ≃* elementaryProjective K (r + 1) :=
  MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (r + 1))))
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by
        exact (QuotientGroup.ker_mk' (Subgroup.center (elementaryRootGroup K (r + 1)))).trans
          (CFSGOrthogonalBIndexCenter.center_eq_bot K p h2 r)),
      QuotientGroup.mk'_surjective _⟩

@[simp] theorem oddProjectiveEquiv_apply (K : Type) [Field K] (p : ℕ)
    [Fact p.Prime] [CharP K p] (h2 : (2 : K) ≠ 0) (r : ℕ)
    (g : elementaryRootGroup K (r + 1)) :
    oddProjectiveEquiv K p h2 r g =
      QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (r + 1))) g := rfl

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
