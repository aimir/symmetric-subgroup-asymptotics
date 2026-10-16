import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenFourByFourCharts
import SymmetricSubgroupAsymptotics.ProductBlockMatchingClosure
import Mathlib.GroupTheory.PGroup

/-! A four-fibre action with matching labels carried faithfully by its
actual top has binary original block kernel. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace ProductFourPointMatchingKernel
open PrimitiveAffineDegreeTwoZeroSixteenFourByFourCharts (matchingColor)

private theorem matching_fixed_involution (f : Fin 4 → Fin 4)
    (hf : Function.Injective f)
    (hmatch : ∀ x y : Fin 4, x ≠ y → matchingColor (f x) (f y) = matchingColor x y) :
    ∀ x, f (f x) = x := by
  have h : ∀ f : Fin 4 → Fin 4, Function.Injective f →
      (∀ x y : Fin 4, x ≠ y → matchingColor (f x) (f y) = matchingColor x y) →
      ∀ x, f (f x) = x := by decide +kernel
  exact h f hf hmatch

variable {X : Type} {U : Subgroup (Equiv.Perm X)}
    (C : ProductBlockFrame U (Fin 4) (Fin 4))
    (label : Fin 4 → Fin 3 → Fin 4)
    (hlabel : ∀ i, Function.Injective (label i))

abbrev colour (x y : X) : Fin 4 :=
  label (C.frame.symm x).1
    (matchingColor (C.frame.symm x).2 (C.frame.symm y).2)

variable (hmatch : ∀ u : U,
    ProductBlockFrame.MatchingPreserves C.frame (colour C label)
      (u : Equiv.Perm X) (C.top u))

include hlabel hmatch in
theorem kernel_square (u : C.top.ker) : u ^ 2 = 1 := by
  have ht : C.top (u : U) = 1 := u.2
  have htop (i x : Fin 4) :
      (C.frame.symm (((u : U) : Equiv.Perm X) (C.frame (i,x)))).1 = i := by
    simpa only [ht,Equiv.Perm.one_apply] using C.intertwine (u : U) (i,x)
  let f (i x : Fin 4) := (C.frame.symm (((u : U) : Equiv.Perm X) (C.frame (i,x)))).2
  have hact (i x : Fin 4) :
      ((u : U) : Equiv.Perm X) (C.frame (i,x)) = C.frame (i,f i x) := by
    apply C.frame.symm.injective
    simp only [C.frame.symm_apply_apply]
    exact Prod.ext (htop i x) rfl
  have hinj (i : Fin 4) : Function.Injective (f i) := by
    intro x y he
    have hp : C.frame (i,x) = C.frame (i,y) := by
      apply (u : Equiv.Perm X).injective
      rw [hact,hact,he]
    exact congrArg Prod.snd (C.frame.injective hp)
  have hfixed (i x y : Fin 4) (hne : x ≠ y) :
      matchingColor (f i x) (f i y) = matchingColor x y := by
    apply hlabel i
    have hd : C.frame (i,x) ≠ C.frame (i,y) := by
      intro he
      exact hne (congrArg Prod.snd (C.frame.injective he))
    have hm := hmatch (u : U) (C.frame (i,x)) (C.frame (i,y))
      (by simp) hd
    rw [hact,hact] at hm
    simpa only [colour,C.frame.symm_apply_apply,ht,Equiv.Perm.one_apply] using hm
  have hinvol (i x : Fin 4) : f i (f i x) = x :=
    matching_fixed_involution (f i) (hinj i) (hfixed i) x
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro z
  obtain ⟨⟨i,x⟩,rfl⟩ := C.frame.surjective z
  change ((u : U) : Equiv.Perm X) (((u : U) : Equiv.Perm X) (C.frame (i,x))) = C.frame (i,x)
  rw [hact,hact,hinvol]

include hlabel hmatch in
theorem kernel_binary : IsPGroup 2 C.top.ker := by
  intro u
  exact ⟨1,by simpa only [pow_one] using kernel_square C label hlabel hmatch u⟩

end ProductFourPointMatchingKernel
end SymmetricSubgroupAsymptotics
end
