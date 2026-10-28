import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Tactic.Group

/-! An equivariant central surjection need not lift every fixed point.
Its fixed image nevertheless contains the target fixed derived subgroup.
If that derived subgroup is perfect, the SOURCE FIXED DERIVED image is
exactly the target fixed derived subgroup. No H1 vanishing, fixed-kernel
hypothesis, finite-group assumption or classification is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CentralSurjectionDerivedFixedImage
variable {G H : Type*} [Group G] [Group H]

def fixed (sigma : G →* G) : Subgroup G := sigma.eqLocus (MonoidHom.id G)

private theorem mem_fixed (sigma : G →* G) (x : G) :
    x ∈ fixed sigma ↔ sigma x = x := Iff.rfl

def fixedMap (f : G →* H) (sigma : G →* G) (tau : H →* H)
    (he : ∀ x, f (sigma x) = tau (f x)) : fixed sigma →* fixed tau where
  toFun x := ⟨f x.val, by
    change tau (f x.val) = f x.val
    exact (he x.val).symm.trans (congrArg f x.property)⟩
  map_one' := Subtype.ext (map_one f)
  map_mul' x y := Subtype.ext (map_mul f x.val y.val)

private def difference (sigma : G →* G) (L : Subgroup G)
    (hc : ∀ x : L, x.val⁻¹ * sigma x.val ∈ Subgroup.center G) :
    L →* Subgroup.center G where
  toFun x := ⟨x.val⁻¹ * sigma x.val, hc x⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by
    apply Subtype.ext
    change (x.val * y.val)⁻¹ * sigma (x.val * y.val) =
      (x.val⁻¹ * sigma x.val) * (y.val⁻¹ * sigma y.val)
    have hm : y.val⁻¹ * (x.val⁻¹ * sigma x.val) =
        (x.val⁻¹ * sigma x.val) * y.val⁻¹ :=
      Subgroup.mem_center_iff.mp (hc x) y.val⁻¹
    calc
      _ = y.val⁻¹ * (x.val⁻¹ * sigma x.val) * sigma y.val := by
        rw [map_mul, mul_inv_rev]
        group
      _ = _ := by rw [hm]; group

/-- The quotient obstruction to fixed lifting is abelian: every target
fixed commutator has an actual source fixed lift. -/
theorem commutator_le_fixed_range (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center G) (sigma : G →* G) (tau : H →* H)
    (he : ∀ x, f (sigma x) = tau (f x)) :
    commutator (fixed tau) ≤ (fixedMap f sigma tau he).range := by
  let L : Subgroup G := (fixed tau).comap f
  let p : L →* fixed tau := {
    toFun := fun x => ⟨f x.val, x.property⟩
    map_one' := Subtype.ext (map_one f)
    map_mul' := fun x y => Subtype.ext (map_mul f x.val y.val) }
  have hp : Function.Surjective p := by
    intro y
    obtain ⟨x, hx⟩ := hf y.val
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    change f x ∈ fixed tau
    exact hx.symm ▸ y.property
  have hc (x : L) : x.val⁻¹ * sigma x.val ∈ Subgroup.center G := by
    apply hker
    change f (x.val⁻¹ * sigma x.val) = 1
    have hx : tau (f x.val) = f x.val := x.property
    rw [map_mul, map_inv, he, hx, inv_mul_cancel]
  letI : CommGroup (Subgroup.center G) :=
    { (inferInstance : Group (Subgroup.center G)) with
      mul_comm := fun x y => Subtype.ext
        ((Subgroup.mem_center_iff.mp x.property) y.val).symm }
  let c := difference sigma L hc
  have hd : commutator L ≤ c.ker := Abelianization.commutator_subset_ker c
  have hm : (commutator L).map p = commutator (fixed tau) := by
    simp only [commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective p hp]
  intro y hy
  rw [← hm] at hy
  obtain ⟨x, hx, hxy⟩ := hy
  have hcx : c x = 1 := hd hx
  have hdx : x.val⁻¹ * sigma x.val = 1 := congrArg Subtype.val hcx
  have hfix : sigma x.val = x.val := (inv_mul_eq_one.mp hdx).symm
  refine ⟨⟨x.val, hfix⟩, ?_⟩
  exact hxy

/-- Perfectness is required only for the actual target FIXED DERIVED
subgroup. It is not inferred from a projective/simple model name. -/
theorem map_commutator_fixed_eq (f : G →* H) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center G) (sigma : G →* G) (tau : H →* H)
    (he : ∀ x, f (sigma x) = tau (f x))
    [Group.IsPerfect (commutator (fixed tau))] :
    (commutator (fixed sigma)).map (fixedMap f sigma tau he) =
      commutator (fixed tau) := by
  rw [map_commutator_eq]
  apply le_antisymm
  · exact Subgroup.commutator_mono le_top le_top
  · calc
      commutator (fixed tau) =
          ⁅commutator (fixed tau), commutator (fixed tau)⁆ :=
        Subgroup.commutator_eq_self.symm
      _ ≤ ⁅(fixedMap f sigma tau he).range, (fixedMap f sigma tau he).range⁆ :=
        Subgroup.commutator_mono (commutator_le_fixed_range f hf hker sigma tau he)
          (commutator_le_fixed_range f hf hker sigma tau he)

end SymmetricSubgroupAsymptotics.CentralSurjectionDerivedFixedImage
