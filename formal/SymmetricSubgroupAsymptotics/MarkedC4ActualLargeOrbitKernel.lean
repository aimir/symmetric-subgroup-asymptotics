import SymmetricSubgroupAsymptotics.MarkedC4OrbitCutoffFamilies
import Mathlib.GroupTheory.GroupAction.SubMulAction

/-! The actual kernel used in the large-orbit reduction. The projection
forgets the small original orbits; its kernel is retained as a subgroup on
the same original points. It has only small orbits, including fixed points
on the omitted large orbits. No encoding or counting bound is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualLargeOrbitKernel

variable {b : ℕ} (G : Subgroup (Equiv.Perm (Fin b))) (C : ℕ)

def largePoints : SubMulAction G (Fin b) where
  carrier := {x | C ≤ Nat.card (MulAction.orbit G x)}
  smul_mem' g x hx := by
    change C ≤ Nat.card (MulAction.orbit G (g • x))
    simpa only [MulAction.orbit_smul] using hx

def projection : G →* Equiv.Perm (largePoints G C) :=
  MulAction.toPermHom G (largePoints G C)

/-- The original permutation subgroup, rather than a relabelled quotient. -/
def retained : Subgroup (Equiv.Perm (Fin b)) :=
  (projection G C).ker.map G.subtype

theorem retained_le : retained G C ≤ G := by
  rintro _ ⟨g, _, rfl⟩
  exact g.property

theorem fixes_large {x : Fin b}
    (hx : C ≤ Nat.card (MulAction.orbit G x))
    {g : Equiv.Perm (Fin b)} (hg : g ∈ retained G C) : g x = x := by
  obtain ⟨a, ha, rfl⟩ := hg
  have he : projection G C a = 1 := ha
  exact congrArg (fun p : Equiv.Perm (largePoints G C) =>
    (p ⟨x, hx⟩).val) he

theorem large_orbit_card_one {x : Fin b}
    (hx : C ≤ Nat.card (MulAction.orbit G x)) :
    Nat.card (MulAction.orbit (retained G C) x) = 1 := by
  have ho : MulAction.orbit (retained G C) x = {x} := by
    ext y
    constructor
    · rintro ⟨g, rfl⟩
      exact Set.mem_singleton_iff.mpr (fixes_large G C hx g.property)
    · intro hy
      have he : y = x := Set.mem_singleton_iff.mp hy
      subst y
      exact MulAction.mem_orbit_self x
  rw [ho]
  simp

theorem orbit_card_le_original (x : Fin b) :
    Nat.card (MulAction.orbit (retained G C) x) ≤
      Nat.card (MulAction.orbit G x) := by
  let f : MulAction.orbit (retained G C) x → MulAction.orbit G x := fun y =>
    ⟨y.val, by
      obtain ⟨g, hg⟩ := y.property
      exact ⟨⟨g.val, retained_le G C g.property⟩, hg⟩⟩
  have hf : Function.Injective f := by
    intro y z h
    exact Subtype.ext (congrArg (fun u : MulAction.orbit G x => u.val) h)
  exact Nat.card_le_card_of_injective f hf

/-- Every retained orbit is strictly below the same cutoff. -/
theorem orbitCutoff (hC : 2 ≤ C) :
    OrbitCutoffFamilies.OrbitCutoff C (retained G C) := by
  intro x
  by_cases hx : C ≤ Nat.card (MulAction.orbit G x)
  · rw [large_orbit_card_one G C hx]
    omega
  · exact (orbit_card_le_original G C x).trans_lt (lt_of_not_ge hx)

/-- The target core belongs to the same bounded-orbit soluble family used
by the fixed-cutoff reduction. -/
def solubleTarget [IsSolvable G] (hC : 2 ≤ C) :
    OrbitCutoffFamilies.SolubleFamily C b := by
  letI : IsSolvable (retained G C) :=
    solvable_of_solvable_injective
      (f := Subgroup.inclusion (retained_le G C))
      (Subgroup.inclusion_injective _)
  exact ⟨retained G C, inferInstance, orbitCutoff G C hC⟩

end SymmetricSubgroupAsymptotics.MarkedC4.ActualLargeOrbitKernel
end
