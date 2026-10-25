import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.GroupAction.Hom

/-! An actual action on a surjective equivariant quotient factors
through every surjective source homomorphism already acting on the
original point set. This supplies the induced block action on a literal
component image; it is not an action-recognition hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SurjectiveEquivariantActionFactor

variable {G H Ω X : Type} [Group G] [Group H]
    [MulAction G Ω] [MulAction G X] [MulAction H Ω]
    (φ : G →* H) (hφ : Function.Surjective φ)
    (p : Ω → X) (hp : Function.Surjective p)
    (heq : ∀ (g : G) (ω : Ω), p (g • ω) = g • p ω)
    (hact : ∀ (g : G) (ω : Ω), φ g • ω = g • ω)

include hp heq hact in
theorem kernel_le : φ.ker ≤ (MulAction.toPermHom G X).ker := by
  intro g hg
  apply Equiv.ext
  intro x
  obtain ⟨ω,rfl⟩ := hp x
  change g • p ω = p ω
  rw [← heq g ω]
  have h : g • ω = ω := by
    rw [← hact g ω,MonoidHom.mem_ker.mp hg,one_smul]
  exact congrArg p h

def hom : H →* Equiv.Perm X :=
  φ.liftOfSurjective hφ ⟨MulAction.toPermHom G X,kernel_le φ p hp heq hact⟩

theorem hom_apply (g : G) : hom φ hφ p hp heq hact (φ g) = MulAction.toPermHom G X g := by
  simp only [hom,MonoidHom.liftOfSurjective,MonoidHom.liftOfRightInverse_comp_apply]

abbrev action : MulAction H X := MulAction.compHom X (hom φ hφ p hp heq hact)

theorem equivariant :
    letI := action φ hφ p hp heq hact
    ∀ (h : H) (ω : Ω), p (h • ω) = h • p ω := by
  letI := action φ hφ p hp heq hact
  intro h ω
  obtain ⟨g,rfl⟩ := hφ h
  change p (φ g • ω) = hom φ hφ p hp heq hact (φ g) (p ω)
  rw [hact,hom_apply]
  exact heq g ω

end SymmetricSubgroupAsymptotics.SurjectiveEquivariantActionFactor
