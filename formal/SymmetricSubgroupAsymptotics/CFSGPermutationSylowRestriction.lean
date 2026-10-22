import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Perm.MaximalSubgroups

/-! Restricting an actual symmetric Sylow subgroup to any one of its
invariant subsets gives an actual Sylow subgroup of the full symmetric
group on that subset. The full set stabilizer supplies the surjective
restriction map; the original subgroup and its literal image are retained. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics.CFSGPermutationSylowRestriction

variable {X : Type*} [Finite X] {p : ℕ} [Fact p.Prime]
  (P : Sylow p (Equiv.Perm X)) (s : Set X)
  (hPs : (P : Subgroup (Equiv.Perm X)) ≤ MulAction.stabilizer (Equiv.Perm X) s)

def restrictionHom : P →* Equiv.Perm s :=
  (MulAction.toPermHom (MulAction.stabilizer (Equiv.Perm X) s) s).comp
    (Subgroup.inclusion hPs)

def restrictedSylow : Sylow p (Equiv.Perm s) :=
  (P.subtype hPs).mapSurjective
    (f := MulAction.toPermHom (MulAction.stabilizer (Equiv.Perm X) s) s)
    (Equiv.Perm.stabilizer.surjective_toPerm s)

theorem restrictedSylow_coe : (restrictedSylow P s hPs : Subgroup (Equiv.Perm s)) =
    (restrictionHom P s hPs).range := by
  change ((P : Subgroup (Equiv.Perm X)).subgroupOf
    (MulAction.stabilizer (Equiv.Perm X) s)).map
    (MulAction.toPermHom (MulAction.stabilizer (Equiv.Perm X) s) s) = _
  ext q
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g.val, hg⟩, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨⟨g.val, hPs g.property⟩, g.property, rfl⟩

end SymmetricSubgroupAsymptotics.CFSGPermutationSylowRestriction
