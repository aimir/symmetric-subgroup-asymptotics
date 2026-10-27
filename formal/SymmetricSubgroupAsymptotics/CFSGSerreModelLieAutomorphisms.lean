import SymmetricSubgroupAsymptotics.CFSGSerreRootLieHom

/-! Genuine Lie preservation extends from the original root generators to
EVERY element of the literal original model group. The explicit divided-
power cutoff is an internal generic input, discharged in each root family. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreModelLieAutomorphisms

section General
variable (K L : Type*) [CommRing K] [LieRing L] [LieAlgebra K L]

def preserving : Subgroup (L≃ₗ[K]L) where
  carrier:={g | ∀ x y,g ⁅x,y⁆=⁅g x,g y⁆}
  one_mem':=by intro x y;rfl
  mul_mem':=by
    intro f g hf hg x y
    change f (g ⁅x,y⁆)=⁅f (g x),f (g y)⁆
    rw [hg,hf]
  inv_mem':=by
    intro g hg x y
    change g.symm ⁅x,y⁆=⁅g.symm x,g.symm y⁆
    apply g.injective
    rw [LinearEquiv.apply_symm_apply]
    simpa only [LinearEquiv.apply_symm_apply] using (hg (g.symm x) (g.symm y)).symm
end General

open CFSG.Models.Chevalley
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (K : Type) [Field K]
  (hge : ∀ neg i k,4 ≤ k→integralOperator A neg i k=0)

include hge in
theorem model_preserves_lie (g : Model A K) (x y : Space A K) :
    g.val ⁅x,y⁆=⁅g.val x,g.val y⁆ := by
  have hle : subgroup A K≤preserving K (Space A K) := by
    apply (Subgroup.closure_le _).mpr
    rintro f ⟨neg,i,t,hf⟩
    intro u v
    change f.toLinearMap ⁅u,v⁆=⁅f.toLinearMap u,f.toLinearMap v⁆
    rw [hf]
    exact CFSGSerreRootLieHom.rootOperator_map_lie A K neg i (hge neg i) t u v
  exact hle g.property x y

def modelLieHom (hge : ∀ neg i k,4 ≤ k→integralOperator A neg i k=0) (g : Model A K) : Space A K→ₗ⁅K⁆Space A K where
  toLinearMap:=g.val.toLinearMap
  map_lie':=fun {x y}=>model_preserves_lie A K hge g x y

@[simp] theorem modelLieHom_apply (g : Model A K) (x : Space A K) :
    modelLieHom A K hge g x=g.val x := rfl

end SymmetricSubgroupAsymptotics.CFSGSerreModelLieAutomorphisms
