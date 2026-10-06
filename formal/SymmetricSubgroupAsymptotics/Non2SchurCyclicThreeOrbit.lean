import SymmetricSubgroupAsymptotics.Non2SchurCyclicSevenOrbit

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
attribute [local instance] Fintype.ofFinite

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

section ScalarGeneric

variable {k G₀ B₀ X₀ A₀ : Type} [Field k] [Finite k]
  [Group G₀] [Finite G₀] [Group B₀] [Finite B₀]
  [Finite X₀] [MulAction G₀ X₀] [MulAction.IsPretransitive G₀ X₀]
  [AddCommGroup A₀] [Module k A₀]

omit [Finite B₀] in
/-- Scalar-generic form of the cyclic-three image theorem.  The hypotheses
record the literal two-dimensional, Schur-dimension-one row and the fact
that the ground field has two elements, rather than changing its scalar
type by dependent elimination. -/
theorem schurSimpleActionEndRepresentation_generic_range_card_eq_three
    [FiniteDimensional k A₀]
    (hcardk : Nat.card k = 2)
    (sigma : Representation k B₀ A₀)
    (S : Submodule k[B₀] sigma.asModule)
    [IsSimpleModule k[B₀] S]
    (hnonfixed : ¬ representationSubmoduleFixed sigma S)
    (hS : Module.finrank k S = 2)
    (hSE : Module.finrank (Module.End k[B₀] S) S = 1) :
    Nat.card (MonoidHom.toHomUnits
      (schurSimpleActionEndRepresentation_generic sigma S)).range = 3 := by
  classical
  let E := Module.End k[B₀] S
  letI : FiniteDimensional k S :=
    FiniteDimensional.of_injective
      (S.subtype.restrictScalars k) S.subtype_injective
  letI : Nontrivial S := IsSimpleModule.nontrivial k[B₀] S
  letI : Finite S := Module.finite_of_finite k
  have hE : Module.finrank k E = 2 := by
    have htower := schur_simple_finrank_tower
      (k := k) (R := k[B₀]) (X := S)
    rw [hS, hSE, Nat.mul_one] at htower
    exact htower.symm
  letI : FiniteDimensional k E :=
    FiniteDimensional.of_finrank_eq_succ hE
  letI : Finite E := Module.finite_of_finite k
  letI : Field E := littleWedderburn E
  letI : FiniteDimensional E S :=
    FiniteDimensional.of_finrank_eq_succ hSE
  have hEcard : Nat.card E = 4 := by
    have hcard : Nat.card E = Nat.card k ^ Module.finrank k E :=
      Module.natCard_eq_pow_finrank
    rw [hcard, hE, hcardk]
    norm_num
  have hEndFinrank : Module.finrank E (Module.End E S) = 1 := by
    rw [Module.finrank_linearMap, hSE]
  let eEnd : E ≃+* Module.End E S :=
    RingEquiv.ofBijective (algebraMap E (Module.End E S))
      (Module.Free.bijective_algebraMap_of_finrank_eq_one
        (R := E) (S := Module.End E S) hEndFinrank)
  have hGL : Nat.card (Module.End E S)ˣ = 3 := by
    rw [← Nat.card_congr (Units.mapEquiv eEnd.toMulEquiv).toEquiv,
      Nat.card_units, hEcard]
  let rhoE := MonoidHom.toHomUnits
    (schurSimpleActionEndRepresentation_generic sigma S)
  have hdvd : Nat.card rhoE.range ∣ 3 := by
    rw [← hGL]
    exact Subgroup.card_subgroup_dvd_card rhoE.range
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with hrange | hrange
  · have hindex : rhoE.ker.index = 1 := by
      rw [Subgroup.index_ker, hrange]
    have hkerTop : rhoE.ker = ⊤ := Subgroup.index_eq_one.mp hindex
    have hfixed : representationSubmoduleFixed sigma S := by
      intro g x
      apply (mem_schurSimpleActionKernel_iff sigma S g).mp
      rw [← schurSimpleActionEndRepresentation_generic_ker sigma S,
        ← MonoidHom.ker_toHomUnits, hkerTop]
      exact Subgroup.mem_top g
    exact (hnonfixed hfixed).elim
  · exact hrange

omit [Finite G₀] [Finite B₀] [Finite X₀] in
/-- Pulling a scalar `(2,1)` row back through an onto map gives one or
three kernel orbits in the original transitive action. -/
theorem schurSimpleActionKernel_comap_orbit_classes_eq_one_or_three_generic
    [FiniteDimensional k A₀]
    (hcardk : Nat.card k = 2)
    (x : X₀)
    (sigma : Representation k B₀ A₀)
    (S : Submodule k[B₀] sigma.asModule)
    [IsSimpleModule k[B₀] S]
    (phi : G₀ →* B₀) (hphi : Function.Surjective phi)
    (hnonfixed : ¬ representationSubmoduleFixed sigma S)
    (hS : Module.finrank k S = 2)
    (hSE : Module.finrank (Module.End k[B₀] S) S = 1) :
    Nat.card (MulAction.orbitRel.Quotient
      ((schurSimpleActionKernel sigma S).comap phi) X₀) = 1 ∨
    Nat.card (MulAction.orbitRel.Quotient
      ((schurSimpleActionKernel sigma S).comap phi) X₀) = 3 := by
  let rhoE := MonoidHom.toHomUnits
    (schurSimpleActionEndRepresentation_generic sigma S)
  let f : G₀ →* (Module.End (Module.End k[B₀] S) S)ˣ :=
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
    exact schurSimpleActionEndRepresentation_generic_range_card_eq_three
      hcardk sigma S hnonfixed hS hSE
  let fr : G₀ →* f.range := f.rangeRestrict
  have hker : f.ker = (schurSimpleActionKernel sigma S).comap phi := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_comap,
      ← schurSimpleActionEndRepresentation_generic_ker sigma S,
      ← MonoidHom.ker_toHomUnits]
    rfl
  have hclasses := kernel_orbit_classes_card_eq_image_index
    (G := G₀) (X := X₀) x fr (by
      simpa only [fr] using f.rangeRestrict_surjective)
  have hdvd : ((MulAction.stabilizer G₀ x).map fr).index ∣ 3 := by
    rw [← hcard]
    exact ((MulAction.stabilizer G₀ x).map fr).index_dvd_card
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with hi | hi
  · left
    rw [← hclasses, MonoidHom.ker_rangeRestrict, hker] at hi
    exact hi
  · right
    rw [← hclasses, MonoidHom.ker_rangeRestrict, hker] at hi
    exact hi

omit [Finite G₀] [Finite B₀] [Finite X₀] in
/-- On eight or sixteen blocks, the three-orbit alternative is impossible. -/
theorem schurSimpleActionKernel_comap_orbit_classes_eq_one_of_card_eight_or_sixteen_generic
    [FiniteDimensional k A₀]
    (hcardk : Nat.card k = 2)
    (x : X₀)
    (sigma : Representation k B₀ A₀)
    (S : Submodule k[B₀] sigma.asModule)
    [IsSimpleModule k[B₀] S]
    (phi : G₀ →* B₀) (hphi : Function.Surjective phi)
    (hnonfixed : ¬ representationSubmoduleFixed sigma S)
    (hS : Module.finrank k S = 2)
    (hSE : Module.finrank (Module.End k[B₀] S) S = 1)
    (hs : Nat.card X₀ = 8 ∨ Nat.card X₀ = 16) :
    Nat.card (MulAction.orbitRel.Quotient
      ((schurSimpleActionKernel sigma S).comap phi) X₀) = 1 := by
  rcases schurSimpleActionKernel_comap_orbit_classes_eq_one_or_three_generic
      hcardk x sigma S phi hphi hnonfixed hS hSE with hone | hthree
  · exact hone
  · have hprod := normal_orbit_card_mul_classes
        ((schurSimpleActionKernel sigma S).comap phi) x
    rw [hthree] at hprod
    rcases hs with hs | hs <;> rw [hs] at hprod <;> omega

end ScalarGeneric

end SymmetricSubgroupAsymptotics

end
