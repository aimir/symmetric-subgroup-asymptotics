import SymmetricSubgroupAsymptotics.Non2SchurScalarOrbit
import Mathlib.Tactic.NormNum.Prime

/-!
# The three-dimensional scalar Schur row has cyclic-seven image

For a binary simple row of ground dimension three and Schur dimension one,
the Schur division ring has eight elements.  The nonfixed original action
therefore has image the full seven-element unit group.  On a transitive
action of degree eight or sixteen, the row kernel is itself transitive:
its orbit count divides seven and also partitions a power-of-two set into
equal parts.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open scoped Classical MonoidAlgebra
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics

variable {B X A : Type} [Group B]
  [AddCommGroup A] [Module (ZMod 2) A]

/-- A nonfixed `(h,e)=(3,1)` row acts through the complete seven-element
unit group of its Schur field. -/
theorem schurSimpleActionEndRepresentation_range_card_eq_seven
    [Finite B] [FiniteDimensional (ZMod 2) A]
    (sigma : Representation (ZMod 2) B A)
    (S : Submodule (ZMod 2)[B] sigma.asModule)
    [IsSimpleModule (ZMod 2)[B] S]
    (hnonfixed : ¬ representationSubmoduleFixed sigma S)
    (hS : Module.finrank (ZMod 2) S = 3)
    (hSE : Module.finrank (Module.End (ZMod 2)[B] S) S = 1) :
    Nat.card (MonoidHom.toHomUnits
      (schurSimpleActionEndRepresentation sigma S)).range = 7 := by
  classical
  let E := Module.End (ZMod 2)[B] S
  letI : FiniteDimensional (ZMod 2) S :=
    FiniteDimensional.of_injective
      (S.subtype.restrictScalars (ZMod 2)) S.subtype_injective
  letI : Nontrivial S := IsSimpleModule.nontrivial (ZMod 2)[B] S
  letI : Finite S := Module.finite_of_finite (ZMod 2)
  have hE : Module.finrank (ZMod 2) E = 3 := by
    have htower := schur_simple_finrank_tower
      (k := ZMod 2) (R := (ZMod 2)[B]) (X := S)
    rw [hS, hSE, mul_one] at htower
    exact htower.symm
  letI : FiniteDimensional (ZMod 2) E :=
    FiniteDimensional.of_finrank_eq_succ hE
  letI : Finite E := Module.finite_of_finite (ZMod 2)
  letI : Field E := littleWedderburn E
  letI : FiniteDimensional E S :=
    FiniteDimensional.of_finrank_eq_succ hSE
  have hEcard : Nat.card E = 8 := by
    have hcard : Nat.card E = Nat.card (ZMod 2) ^
        Module.finrank (ZMod 2) E := Module.natCard_eq_pow_finrank
    rw [hcard, hE, Nat.card_zmod]
    norm_num
  have hEndFinrank : Module.finrank E (Module.End E S) = 1 := by
    rw [Module.finrank_linearMap, hSE]
  let eEnd : E ≃+* Module.End E S :=
    RingEquiv.ofBijective (algebraMap E (Module.End E S))
      (Module.Free.bijective_algebraMap_of_finrank_eq_one
        (R := E) (S := Module.End E S) hEndFinrank)
  have hGL : Nat.card (Module.End E S)ˣ = 7 := by
    rw [← Nat.card_congr (Units.mapEquiv eEnd.toMulEquiv).toEquiv,
      Nat.card_units, hEcard]
  let rhoE := MonoidHom.toHomUnits
    (schurSimpleActionEndRepresentation sigma S)
  have hdvd : Nat.card rhoE.range ∣ 7 := by
    rw [← hGL]
    exact Subgroup.card_subgroup_dvd_card rhoE.range
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hdvd with hrange | hrange
  · have hindex : rhoE.ker.index = 1 := by
      rw [Subgroup.index_ker, hrange]
    have hkerTop : rhoE.ker = ⊤ := Subgroup.index_eq_one.mp hindex
    have hfixed : representationSubmoduleFixed sigma S := by
      intro g x
      apply (mem_schurSimpleActionKernel_iff sigma S g).mp
      rw [← schurSimpleActionEndRepresentation_ker sigma S,
        ← MonoidHom.ker_toHomUnits, hkerTop]
      exact Subgroup.mem_top g
    exact (hnonfixed hfixed).elim
  · exact hrange

/-- The row kernel has one or seven orbits in every original transitive
action. -/
theorem schurSimpleActionKernel_orbit_classes_eq_one_or_seven
    [Finite B] [Finite X] [MulAction B X]
    [MulAction.IsPretransitive B X]
    [FiniteDimensional (ZMod 2) A]
    (x : X)
    (sigma : Representation (ZMod 2) B A)
    (S : Submodule (ZMod 2)[B] sigma.asModule)
    [IsSimpleModule (ZMod 2)[B] S]
    (hnonfixed : ¬ representationSubmoduleFixed sigma S)
    (hS : Module.finrank (ZMod 2) S = 3)
    (hSE : Module.finrank (Module.End (ZMod 2)[B] S) S = 1) :
    Nat.card (MulAction.orbitRel.Quotient
      (schurSimpleActionKernel sigma S) X) = 1 ∨
    Nat.card (MulAction.orbitRel.Quotient
      (schurSimpleActionKernel sigma S) X) = 7 := by
  let rhoE := MonoidHom.toHomUnits
    (schurSimpleActionEndRepresentation sigma S)
  let f : B →* rhoE.range := rhoE.rangeRestrict
  have hcard : Nat.card rhoE.range = 7 :=
    schurSimpleActionEndRepresentation_range_card_eq_seven
      sigma S hnonfixed hS hSE
  have hclasses := kernel_orbit_classes_card_eq_image_index
    (G := B) (X := X) x f (by
      simpa [f] using rhoE.rangeRestrict_surjective)
  have hdvd : ((MulAction.stabilizer B x).map f).index ∣ 7 := by
    rw [← hcard]
    exact ((MulAction.stabilizer B x).map f).index_dvd_card
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hdvd with hi | hi
  · left
    rw [← hclasses, MonoidHom.ker_rangeRestrict,
      MonoidHom.ker_toHomUnits,
      schurSimpleActionEndRepresentation_ker] at hi
    exact hi
  · right
    rw [← hclasses, MonoidHom.ker_rangeRestrict,
      MonoidHom.ker_toHomUnits,
      schurSimpleActionEndRepresentation_ker] at hi
    exact hi

/-- At the two degree-four residual frame sizes, the seven-orbit
alternative is arithmetically impossible. -/
theorem schurSimpleActionKernel_orbit_classes_eq_one_of_card_eight_or_sixteen
    [Finite B] [Finite X] [MulAction B X]
    [MulAction.IsPretransitive B X]
    [FiniteDimensional (ZMod 2) A]
    (x : X)
    (sigma : Representation (ZMod 2) B A)
    (S : Submodule (ZMod 2)[B] sigma.asModule)
    [IsSimpleModule (ZMod 2)[B] S]
    (hnonfixed : ¬ representationSubmoduleFixed sigma S)
    (hS : Module.finrank (ZMod 2) S = 3)
    (hSE : Module.finrank (Module.End (ZMod 2)[B] S) S = 1)
    (hs : Nat.card X = 8 ∨ Nat.card X = 16) :
    Nat.card (MulAction.orbitRel.Quotient
      (schurSimpleActionKernel sigma S) X) = 1 := by
  rcases schurSimpleActionKernel_orbit_classes_eq_one_or_seven
      x sigma S hnonfixed hS hSE with hone | hseven
  · exact hone
  · have hprod := normal_orbit_card_mul_classes
        (schurSimpleActionKernel sigma S) x
    rw [hseven] at hprod
    rcases hs with hs | hs <;> rw [hs] at hprod <;> omega

/-- Pull the scalar row back along an onto original-group map.  Its literal
kernel still has one or seven orbits in every transitive original action;
no action of the quotient group on the original point set is required. -/
theorem schurSimpleActionKernel_comap_orbit_classes_eq_one_or_seven
    {G : Type} [Group G] [Finite G]
    [Finite B] [Finite X] [MulAction G X]
    [MulAction.IsPretransitive G X]
    [FiniteDimensional (ZMod 2) A]
    (x : X)
    (sigma : Representation (ZMod 2) B A)
    (S : Submodule (ZMod 2)[B] sigma.asModule)
    [IsSimpleModule (ZMod 2)[B] S]
    (phi : G →* B) (hphi : Function.Surjective phi)
    (hnonfixed : ¬ representationSubmoduleFixed sigma S)
    (hS : Module.finrank (ZMod 2) S = 3)
    (hSE : Module.finrank (Module.End (ZMod 2)[B] S) S = 1) :
    Nat.card (MulAction.orbitRel.Quotient
      ((schurSimpleActionKernel sigma S).comap phi) X) = 1 ∨
    Nat.card (MulAction.orbitRel.Quotient
      ((schurSimpleActionKernel sigma S).comap phi) X) = 7 := by
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
  have hcard : Nat.card f.range = 7 := by
    rw [hrange]
    exact schurSimpleActionEndRepresentation_range_card_eq_seven
      sigma S hnonfixed hS hSE
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
  have hdvd : ((MulAction.stabilizer G x).map fr).index ∣ 7 := by
    rw [← hcard]
    exact ((MulAction.stabilizer G x).map fr).index_dvd_card
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hdvd with hi | hi
  · left
    rw [← hclasses, MonoidHom.ker_rangeRestrict, hker] at hi
    exact hi
  · right
    rw [← hclasses, MonoidHom.ker_rangeRestrict, hker] at hi
    exact hi

/-- At the actual degree-four frame sizes the pulled-back cyclic-seven row
kernel is transitive on the original blocks. -/
theorem schurSimpleActionKernel_comap_orbit_classes_eq_one_of_card_eight_or_sixteen
    {G : Type} [Group G] [Finite G]
    [Finite B] [Finite X] [MulAction G X]
    [MulAction.IsPretransitive G X]
    [FiniteDimensional (ZMod 2) A]
    (x : X)
    (sigma : Representation (ZMod 2) B A)
    (S : Submodule (ZMod 2)[B] sigma.asModule)
    [IsSimpleModule (ZMod 2)[B] S]
    (phi : G →* B) (hphi : Function.Surjective phi)
    (hnonfixed : ¬ representationSubmoduleFixed sigma S)
    (hS : Module.finrank (ZMod 2) S = 3)
    (hSE : Module.finrank (Module.End (ZMod 2)[B] S) S = 1)
    (hs : Nat.card X = 8 ∨ Nat.card X = 16) :
    Nat.card (MulAction.orbitRel.Quotient
      ((schurSimpleActionKernel sigma S).comap phi) X) = 1 := by
  rcases schurSimpleActionKernel_comap_orbit_classes_eq_one_or_seven
      x sigma S phi hphi hnonfixed hS hSE with hone | hseven
  · exact hone
  · have hprod := normal_orbit_card_mul_classes
        ((schurSimpleActionKernel sigma S).comap phi) x
    rw [hseven] at hprod
    rcases hs with hs | hs <;> rw [hs] at hprod <;> omega

end SymmetricSubgroupAsymptotics

end
