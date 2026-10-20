import SymmetricSubgroupAsymptotics.MarkedC4ActualLargeOrbitKernel

/-! The image used in the large-orbit step has precisely the original
large orbits. Both orbit cardinalities and the relative generators below
refer to the literal projection, rather than an abstract group of the same
order. No generator estimate or encoding estimate is assumed here. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualLargeOrbitImage

open ActualLargeOrbitKernel
variable {b : ℕ} (G : Subgroup (Equiv.Perm (Fin b))) (C : ℕ)

/-- Forgetting the point subtype identifies an image orbit with the same
original orbit. The image is the range of the actual large-point action. -/
def orbitEquiv (x : largePoints G C) :
    MulAction.orbit (projection G C).range x ≃ MulAction.orbit G x.val := by
  let f : MulAction.orbit (projection G C).range x → MulAction.orbit G x.val :=
    fun y => ⟨y.val.val, by
      obtain ⟨g, hg⟩ := y.property
      obtain ⟨a, ha⟩ := g.property
      refine ⟨a, ?_⟩
      have hh := congrArg (fun z : largePoints G C => z.val) hg
      change (g.val x).val = y.val.val at hh
      rw [← ha] at hh
      exact hh⟩
  apply Equiv.ofBijective f
  constructor
  · intro y z h
    apply Subtype.ext
    exact Subtype.ext (congrArg (fun v : MulAction.orbit G x.val => v.val) h)
  · intro y
    obtain ⟨a, ha⟩ := y.property
    let z : MulAction.orbit (projection G C).range x :=
      ⟨projection G C a x, ⟨⟨projection G C a, ⟨a, rfl⟩⟩, rfl⟩⟩
    exact ⟨z, Subtype.ext ha⟩

theorem orbit_card (x : largePoints G C) :
    Nat.card (MulAction.orbit (projection G C).range x) =
      Nat.card (MulAction.orbit G x.val) :=
  Nat.card_congr (orbitEquiv G C x)

/-- Every image orbit has at least the selected cutoff; there are no
spurious fixed points introduced by relabelling the original action. -/
theorem orbit_lower (x : largePoints G C) :
    C ≤ Nat.card (MulAction.orbit (projection G C).range x) := by
  rw [orbit_card]
  exact x.property

theorem degree_le : Nat.card (largePoints G C) ≤ b := by
  simpa using Nat.card_le_card_of_injective
    (fun x : largePoints G C => x.val) Subtype.val_injective

end SymmetricSubgroupAsymptotics.MarkedC4.ActualLargeOrbitImage
end
