import SymmetricSubgroupAsymptotics.CentralSurjectionDerivedFixedImage
import SymmetricSubgroupAsymptotics.CentralSurjectionPerfectTargetCenter

/-! The exact derived-fixed/full-centre comparison induced by an actual
equivariant central surjection. Fixed-point surjectivity is NOT assumed.
The only perfectness input concerns the genuine target fixed derived
subgroup; applications must prove it for their actual native carrier. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CentralSurjectionDerivedFixedCenterEquivalence
open CentralSurjectionDerivedFixedImage
variable {G H : Type*} [Group G] [Group H]
variable (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center G) (sigma : G →* G) (tau : H →* H)
    (he : ∀ x, f (sigma x) = tau (f x))
    [Group.IsPerfect (commutator (fixed tau))]

def derivedMap : commutator (fixed sigma) →* commutator (fixed tau) where
  toFun x := ⟨fixedMap f sigma tau he x.val, by
    rw [← map_commutator_fixed_eq f hf hker sigma tau he]
    exact ⟨x.val, x.property, rfl⟩⟩
  map_one' := Subtype.ext (map_one (fixedMap f sigma tau he))
  map_mul' x y := Subtype.ext (map_mul (fixedMap f sigma tau he) x.val y.val)

theorem derivedMap_surjective : Function.Surjective (derivedMap f hf hker sigma tau he) := by
  intro y
  have hy : y.val ∈ (commutator (fixed sigma)).map (fixedMap f sigma tau he) := by
    rw [map_commutator_fixed_eq f hf hker sigma tau he]
    exact y.property
  obtain ⟨x, hx, hxy⟩ := hy
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

theorem derivedMap_ker_le_center :
    (derivedMap f hf hker sigma tau he).ker ≤ Subgroup.center _ := by
  intro x hx
  have hfx : f x.val.val = 1 :=
    congrArg (fun y : commutator (fixed tau) => y.val.val) hx
  have hz : x.val.val ∈ Subgroup.center G := hker hfx
  apply Subgroup.mem_center_iff.mpr
  intro y
  apply Subtype.ext
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp hz y.val.val

/-- Neither fixed group nor the source fixed derived group is presumed
perfect. The target fixed derived perfectness is the exact needed input. -/
def derivedCenterEquiv :
    (commutator (fixed sigma)) ⧸ Subgroup.center (commutator (fixed sigma)) ≃*
      (commutator (fixed tau)) ⧸ Subgroup.center (commutator (fixed tau)) :=
  CentralSurjectionPerfectTargetCenter.projectiveEquiv
    (derivedMap f hf hker sigma tau he)
    (derivedMap_surjective f hf hker sigma tau he)
    (derivedMap_ker_le_center f hf hker sigma tau he)

end SymmetricSubgroupAsymptotics.CentralSurjectionDerivedFixedCenterEquivalence
