import SymmetricSubgroupAsymptotics.SingletonExtension

/-!
# Exact singleton extension counting for fixed-point-free sources

The general singleton construction is only a surjective presentation because
a source may already have global fixed points.  For a fixed-point-free source,
the added point is the unique global fixed point.  Consequently both the point
and the original source subgroup are recovered from the physical extension.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.SingletonExtensionExact

open SingletonExtension

variable {α X F : Type*}

theorem decode_injective
    (charts : X → X ≃ Option α) (hcharts : ∀ x, charts x x = none)
    (value : F → Subgroup (Equiv.Perm α))
    (hvalue : Function.Injective value)
    (hnofix : ∀ f : F, ∀ a : α, ∃ g : value f, (g : Equiv.Perm α) a ≠ a) :
    Function.Injective (SingletonExtension.decode charts value) := by
  rintro ⟨x,f⟩ ⟨y,g⟩ h
  have hgroups :
      (value f).map (extensionHom (charts x)) =
        (value g).map (extensionHom (charts y)) :=
    congrArg Subtype.val h
  have hxy : x = y := by
    by_contra hne
    cases hcx : charts y x with
    | none =>
        have heq : x = y := (charts y).injective (hcx.trans (hcharts y).symm)
        exact hne heq
    | some a =>
        obtain ⟨u,hmove⟩ := hnofix g a
        have huRight : extensionHom (charts y) u.val ∈
            (value g).map (extensionHom (charts y)) :=
          Subgroup.mem_map.mpr ⟨u.val,u.property,rfl⟩
        have huLeft : extensionHom (charts y) u.val ∈
            (value f).map (extensionHom (charts x)) := by
          rw [hgroups]
          exact huRight
        obtain ⟨v,hv,hvu⟩ := Subgroup.mem_map.mp huLeft
        have hvfix : extensionHom (charts x) v x = x :=
          extensionHom_fixes (charts x) x (hcharts x) v
        have hufix : extensionHom (charts y) u.val x = x := by
          rw [← hvu]
          exact hvfix
        have hc : Option.map u.val (charts y x) = charts y x := by
          simpa only [extensionHom_apply, Equiv.apply_symm_apply] using
            congrArg (charts y) hufix
        have hua : u.val a = a := by
          simpa only [hcx, Option.map_some, Option.some.injEq] using hc
        exact hmove hua
  subst y
  have hfg : f = g := hvalue (map_injective (charts x) hgroups)
  subst g
  rfl

def presentationEquiv
    (charts : X → X ≃ Option α) (hcharts : ∀ x, charts x x = none)
    (value : F → Subgroup (Equiv.Perm α))
    (hvalue : Function.Injective value)
    (hnofix : ∀ f : F, ∀ a : α, ∃ g : value f, (g : Equiv.Perm α) a ≠ a) :
    X × F ≃ SingletonExtension.Family charts value :=
  Equiv.ofBijective (SingletonExtension.decode charts value)
    ⟨decode_injective charts hcharts value hvalue hnofix,
      SingletonExtension.decode_surjective charts value⟩

theorem card_family_eq [Finite X] [Finite F]
    (charts : X → X ≃ Option α) (hcharts : ∀ x, charts x x = none)
    (value : F → Subgroup (Equiv.Perm α))
    (hvalue : Function.Injective value)
    (hnofix : ∀ f : F, ∀ a : α, ∃ g : value f, (g : Equiv.Perm α) a ≠ a) :
    Nat.card (SingletonExtension.Family charts value) = Nat.card X * Nat.card F := by
  rw [← Nat.card_congr (presentationEquiv charts hcharts value hvalue hnofix), Nat.card_prod]

end SymmetricSubgroupAsymptotics.SingletonExtensionExact

end
