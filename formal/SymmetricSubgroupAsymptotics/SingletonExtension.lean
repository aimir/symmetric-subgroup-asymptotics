import Mathlib.GroupTheory.Perm.Option
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-! Actual singleton extensions along explicit point charts. The family
is an image of point/source pairs, so overlaps are forgotten. No invariance
of the source family and no fullness or counting premise are assumed.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.SingletonExtension

variable {α X F : Type*}

/-- Extend a permutation by the identity on the new point `none`. -/
def optionHom : Equiv.Perm α →* Equiv.Perm (Option α) where
  toFun := Equiv.optionCongr
  map_one' := Equiv.optionCongr_one
  map_mul' g h := by
    apply Equiv.ext
    intro x
    cases x <;> rfl

theorem optionHom_injective : Function.Injective (optionHom (α := α)) :=
  Equiv.optionCongr_injective

/-- The chart identifies the distinguished point with `none`. -/
def extensionHom (e : X ≃ Option α) : Equiv.Perm α →* Equiv.Perm X :=
  e.symm.permCongrHom.toMonoidHom.comp optionHom

theorem extensionHom_injective (e : X ≃ Option α) :
    Function.Injective (extensionHom e) :=
  e.symm.permCongrHom.injective.comp optionHom_injective

@[simp] theorem extensionHom_apply (e : X ≃ Option α) (g : Equiv.Perm α) (x : X) :
    extensionHom e g x = e.symm (Option.map g (e x)) := rfl

theorem extensionHom_fixes (e : X ≃ Option α) (x : X) (hx : e x = none)
    (g : Equiv.Perm α) : extensionHom e g x = x := by
  rw [extensionHom_apply, hx, Option.map_none]
  exact e.injective (by simpa only [Equiv.apply_symm_apply] using hx.symm)

@[simp] theorem extensionHom_some (e : X ≃ Option α) (g : Equiv.Perm α) (a : α) :
    extensionHom e g (e.symm (some a)) = e.symm (some (g a)) := by
  simp only [extensionHom_apply, Equiv.apply_symm_apply, Option.map_some]

/-- Restriction through the original extension recovers exactly the
original subgroup, including every predicate on that subgroup. -/
theorem comap_map (e : X ≃ Option α) (H : Subgroup (Equiv.Perm α)) :
    (H.map (extensionHom e)).comap (extensionHom e) = H :=
  Subgroup.comap_map_eq_self_of_injective (extensionHom_injective e) H

theorem map_injective (e : X ≃ Option α) :
    Function.Injective (Subgroup.map (extensionHom e)) :=
  Subgroup.map_injective (extensionHom_injective e)

/-- Actual subgroups on the original point set `X`, with existential
point/source witnesses. The charts are data, not extra counted labels. -/
abbrev Family (charts : X → X ≃ Option α)
    (value : F → Subgroup (Equiv.Perm α)) :=
  {K : Subgroup (Equiv.Perm X) //
    ∃ x : X, ∃ f : F, (value f).map (extensionHom (charts x)) = K}

def decode (charts : X → X ≃ Option α) (value : F → Subgroup (Equiv.Perm α)) :
    X × F → Family charts value :=
  fun z => ⟨(value z.2).map (extensionHom (charts z.1)), z.1, z.2, rfl⟩

theorem decode_surjective (charts : X → X ≃ Option α)
    (value : F → Subgroup (Equiv.Perm α)) : Function.Surjective (decode charts value) := by
  rintro ⟨K, x, f, rfl⟩
  exact ⟨(x,f), rfl⟩

/-- Every label is counted once before forgetting duplicate subgroup
images. This bound also holds when the source has further fixed points. -/
theorem card_family_le [Finite X] [Finite F] (charts : X → X ≃ Option α)
    (value : F → Subgroup (Equiv.Perm α)) :
    Nat.card (Family charts value) ≤ Nat.card X * Nat.card F := by
  calc
    _ ≤ Nat.card (X × F) :=
      Nat.card_le_card_of_surjective (decode charts value) (decode_surjective charts value)
    _ = _ := Nat.card_prod X F

theorem family_has_fixed_point (charts : X → X ≃ Option α)
    (hcharts : ∀ x, charts x x = none) (value : F → Subgroup (Equiv.Perm α))
    (K : Family charts value) : ∃ x : X, ∀ g ∈ K.1, g x = x := by
  obtain ⟨x,f,hf⟩ := K.2
  refine ⟨x, ?_⟩
  intro g hg
  rw [← hf] at hg
  obtain ⟨u,_,rfl⟩ := Subgroup.mem_map.mp hg
  exact extensionHom_fixes (charts x) x (hcharts x) u

/-- The standard deletion chart at each actual finite label. -/
abbrev FinFamily (n : ℕ) (value : F → Subgroup (Equiv.Perm (Fin n))) :=
  Family (fun x : Fin (n+1) => finSuccEquiv' x) value

theorem card_finFamily_le [Finite F] (n : ℕ)
    (value : F → Subgroup (Equiv.Perm (Fin n))) :
    Nat.card (FinFamily n value) ≤ (n+1) * Nat.card F := by
  simpa only [Nat.card_fin] using
    card_family_le (fun x : Fin (n+1) => finSuccEquiv' x) value

theorem finFamily_has_fixed_point (n : ℕ)
    (value : F → Subgroup (Equiv.Perm (Fin n))) (K : FinFamily n value) :
    ∃ x : Fin (n+1), ∀ g ∈ K.1, g x = x :=
  family_has_fixed_point _ finSuccEquiv'_at value K

end SymmetricSubgroupAsymptotics.SingletonExtension
