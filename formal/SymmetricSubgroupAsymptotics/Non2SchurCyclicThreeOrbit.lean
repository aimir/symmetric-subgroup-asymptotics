import SymmetricSubgroupAsymptotics.Non2SchurScalarOrbit

/-!
# Pulling back the cyclic-three Schur row

A nonfixed binary simple row of Schur product degree two has literal image
`C3`.  Pulling the row back along an onto map from the original group does
not change that image.  Hence its kernel has one or three orbits in any
transitive original action.  On eight or sixteen points the three-orbit
alternative is arithmetically impossible.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

variable {G B X A : Type} [Group G] [Finite G] [Group B] [Finite B]
  [Finite X] [MulAction G X] [MulAction.IsPretransitive G X]
  [AddCommGroup A] [Module (ZMod 2) A]

omit [Finite G] [Finite X] in
/-- The pulled-back kernel of a nonfixed Schur-product-two row has one or
three orbits in the original transitive action. -/
theorem schurSimpleActionKernel_comap_orbit_classes_eq_one_or_three
    [FiniteDimensional (ZMod 2) A]
    (x : X)
    (sigma : Representation (ZMod 2) B A)
    (S : Submodule (ZMod 2)[B] sigma.asModule)
    [IsSimpleModule (ZMod 2)[B] S]
    (phi : G →* B) (hphi : Function.Surjective phi)
    (hnonfixed : ¬ representationSubmoduleFixed sigma S)
    (hq : schurSimpleProductDegree sigma S = 2) :
    Nat.card (MulAction.orbitRel.Quotient
      ((schurSimpleActionKernel sigma S).comap phi) X) = 1 ∨
    Nat.card (MulAction.orbitRel.Quotient
      ((schurSimpleActionKernel sigma S).comap phi) X) = 3 := by
  let rhoE := MonoidHom.toHomUnits
    (schurSimpleActionEndRepresentation sigma S)
  let f : G →* (Module.End (Module.End (ZMod 2)[B] S) S)ˣ :=
    rhoE.comp phi
  have hrange : f.range = rhoE.range := by
    apply le_antisymm
    · rintro y ⟨g, rfl⟩
      exact ⟨phi g, rfl⟩
    · rintro y ⟨b, rfl⟩
      obtain ⟨g, rfl⟩ := hphi b
      exact ⟨g, rfl⟩
  have hcard : Nat.card f.range = 3 := by
    rw [hrange]
    exact schurSimpleActionEndRepresentation_range_card_eq_three
      sigma S hnonfixed hq
  let fr : G →* f.range := f.rangeRestrict
  have hker : f.ker = (schurSimpleActionKernel sigma S).comap phi := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_comap,
      ← schurSimpleActionEndRepresentation_ker sigma S,
      ← MonoidHom.ker_toHomUnits]
    rfl
  have hclasses := kernel_orbit_classes_card_eq_image_index
    (G := G) (X := X) x fr (by
      simpa only [fr] using f.rangeRestrict_surjective)
  have hdvd : ((MulAction.stabilizer G x).map fr).index ∣ 3 := by
    rw [← hcard]
    exact ((MulAction.stabilizer G x).map fr).index_dvd_card
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with hi | hi
  · left
    rw [← hclasses, MonoidHom.ker_rangeRestrict, hker] at hi
    exact hi
  · right
    rw [← hclasses, MonoidHom.ker_rangeRestrict, hker] at hi
    exact hi

omit [Finite G] [Finite X] in
/-- At the two finite-frame degrees, a pulled-back cyclic-three row kernel
is transitive on the original blocks. -/
theorem schurSimpleActionKernel_comap_orbit_classes_eq_one_of_card_eight_or_sixteen_of_productDegree_two
    [FiniteDimensional (ZMod 2) A]
    (x : X)
    (sigma : Representation (ZMod 2) B A)
    (S : Submodule (ZMod 2)[B] sigma.asModule)
    [IsSimpleModule (ZMod 2)[B] S]
    (phi : G →* B) (hphi : Function.Surjective phi)
    (hnonfixed : ¬ representationSubmoduleFixed sigma S)
    (hq : schurSimpleProductDegree sigma S = 2)
    (hs : Nat.card X = 8 ∨ Nat.card X = 16) :
    Nat.card (MulAction.orbitRel.Quotient
      ((schurSimpleActionKernel sigma S).comap phi) X) = 1 := by
  rcases schurSimpleActionKernel_comap_orbit_classes_eq_one_or_three
      x sigma S phi hphi hnonfixed hq with hone | hthree
  · exact hone
  · have hprod := normal_orbit_card_mul_classes
        ((schurSimpleActionKernel sigma S).comap phi) x
    rw [hthree] at hprod
    rcases hs with hs | hs <;> rw [hs] at hprod <;> omega

end SymmetricSubgroupAsymptotics

end
