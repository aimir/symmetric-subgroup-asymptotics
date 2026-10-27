import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Tactic.FinCases

/-! Necessary relators for the image of one generator while its product
with the other generator is fixed. The second image is h^-1*A. These
identities concern arbitrary homomorphisms and assert no presentation
converse, permutation extension, or finite image capacity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FixedProductRelatorTransport

def pair {H : Type*} (x y : H) : Fin 2 → H := fun i => if i = 0 then x else y

@[simp] theorem pair_zero {H : Type*} (x y : H) : pair x y 0 = x := rfl
@[simp] theorem pair_one {H : Type*} (x y : H) : pair x y 1 = y := rfl

theorem lift_pair_map {H G : Type*} [Group H] [Group G]
    (phi : H →* G) (x y : H) (r : FreeGroup (Fin 2)) :
    phi (FreeGroup.lift (pair x y) r) =
      FreeGroup.lift (pair (phi x) (phi y)) r := by
  exact FreeGroup.lift_unique (phi.comp (FreeGroup.lift (pair x y))) (by
    intro i
    simp only [MonoidHom.comp_apply,FreeGroup.lift_apply_of]
    fin_cases i <;> rfl)

theorem image_second_of_product_eq {H G : Type*} [Group H] [Group G]
    (phi : H →* G) (x y : H) (A : G) (hA : phi (x*y) = A) :
    phi y = (phi x)⁻¹ * A := by
  rw [←hA,map_mul,inv_mul_cancel_left]

theorem relator_transport {H G : Type*} [Group H] [Group G]
    (phi : H →* G) (x y : H) (A : G) (hA : phi (x*y) = A)
    (r : FreeGroup (Fin 2)) (hr : FreeGroup.lift (pair x y) r = 1) :
    FreeGroup.lift (pair (phi x) ((phi x)⁻¹*A)) r = 1 := by
  rw [←image_second_of_product_eq phi x y A hA]
  have h := lift_pair_map phi x y r
  rw [hr,map_one] at h
  exact h.symm

theorem presented_relator (rels : Set (FreeGroup (Fin 2)))
    (r : FreeGroup (Fin 2)) (hr : r ∈ rels) :
    FreeGroup.lift (pair (PresentedGroup.of (rels := rels) 0)
      (PresentedGroup.of (rels := rels) 1)) r = 1 := by
  have he := FreeGroup.lift_unique (PresentedGroup.mk rels)
    (f := pair (PresentedGroup.of (rels := rels) 0) (PresentedGroup.of (rels := rels) 1))
    (x := r) (by intro i; fin_cases i <;> rfl)
  exact he.symm.trans (PresentedGroup.one_of_mem hr)

end SymmetricSubgroupAsymptotics.FixedProductRelatorTransport
