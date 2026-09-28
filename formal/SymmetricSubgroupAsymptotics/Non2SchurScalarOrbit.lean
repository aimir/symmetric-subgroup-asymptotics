import SymmetricSubgroupAsymptotics.Non2SchurActionKernel
import SymmetricSubgroupAsymptotics.NormalSubgroupOrbitIndex
import Mathlib.Data.Fintype.Units
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.LittleWedderburn

/-!
# The scalar Schur row has three-element image

When the binary Schur product degree is two, the selected simple row is
one-dimensional over its four-element Schur division ring.  The original
group action commutes with that ring, so it acts through its one-dimensional
general linear group.  This group has order three.  Nonfixedness makes the
image nontrivial, hence exactly three.

For any transitive permutation action of the original group, the literal row
kernel consequently has one or three orbits.  In degree at least 24 every one
of those orbits has length at least eight.
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

/-- The original action on a simple row is linear over its Schur endomorphism
ring: every module endomorphism commutes with every original group element. -/
def schurSimpleActionEndLinearMap
    (sigma : Representation (ZMod 2) B A)
    (S : Submodule (ZMod 2)[B] sigma.asModule)
    (g : B) :
    Module.End (Module.End (ZMod 2)[B] S) S where
  toFun := schurSimpleActionRepresentation sigma S g
  map_add' x y := (schurSimpleActionRepresentation sigma S g).map_add x y
  map_smul' f x := by
    change MonoidAlgebra.single g (1 : ZMod 2) • f x =
      f (MonoidAlgebra.single g (1 : ZMod 2) • x)
    exact (f.map_smul (MonoidAlgebra.single g (1 : ZMod 2)) x).symm

/-- The same literal action, now represented over the Schur ring. -/
def schurSimpleActionEndRepresentation
    (sigma : Representation (ZMod 2) B A)
    (S : Submodule (ZMod 2)[B] sigma.asModule) :
    Representation (Module.End (ZMod 2)[B] S) B S where
  toFun g := schurSimpleActionEndLinearMap sigma S g
  map_one' := by
    ext x
    simp [schurSimpleActionEndLinearMap, schurSimpleActionRepresentation]
  map_mul' g h := by
    ext x
    simp [schurSimpleActionEndLinearMap, schurSimpleActionRepresentation]

/-- Changing the scalar ring does not change the literal action kernel. -/
theorem schurSimpleActionEndRepresentation_ker
    (sigma : Representation (ZMod 2) B A)
    (S : Submodule (ZMod 2)[B] sigma.asModule) :
    (schurSimpleActionEndRepresentation sigma S).ker =
      schurSimpleActionKernel sigma S := by
  ext g
  rw [mem_schurSimpleActionKernel_iff]
  constructor
  · intro hg x
    have hx := LinearMap.congr_fun (MonoidHom.mem_ker.mp hg) x
    simpa [schurSimpleActionEndRepresentation,
      schurSimpleActionEndLinearMap] using hx
  · intro hg
    apply MonoidHom.mem_ker.mpr
    apply LinearMap.ext
    intro x
    simpa [schurSimpleActionEndRepresentation,
      schurSimpleActionEndLinearMap] using hg x

/-- A nonfixed product-degree-two row has image of order exactly three over
its Schur ring. -/
theorem schurSimpleActionEndRepresentation_range_card_eq_three
    [Finite B] [FiniteDimensional (ZMod 2) A]
    (sigma : Representation (ZMod 2) B A)
    (S : Submodule (ZMod 2)[B] sigma.asModule)
    [IsSimpleModule (ZMod 2)[B] S]
    (hnonfixed : ¬ representationSubmoduleFixed sigma S)
    (hq : schurSimpleProductDegree sigma S = 2) :
    Nat.card (MonoidHom.toHomUnits
      (schurSimpleActionEndRepresentation sigma S)).range = 3 := by
  classical
  let E := Module.End (ZMod 2)[B] S
  letI : FiniteDimensional (ZMod 2) S :=
    FiniteDimensional.of_injective
      (S.subtype.restrictScalars (ZMod 2)) S.subtype_injective
  letI : Nontrivial S := IsSimpleModule.nontrivial (ZMod 2)[B] S
  letI : Finite S := Module.finite_of_finite (ZMod 2)
  obtain ⟨hS, hSE⟩ := schurSimpleProductDegree_eq_two_profile
    sigma S hnonfixed hq
  have hE : Module.finrank (ZMod 2) E = 2 :=
    schurSimpleProductDegree_eq_two_end_finrank sigma S hnonfixed hq
  letI : FiniteDimensional (ZMod 2) E :=
    FiniteDimensional.of_finrank_eq_succ hE
  letI : Finite E := Module.finite_of_finite (ZMod 2)
  letI : Field E := littleWedderburn E
  letI : FiniteDimensional E S :=
    FiniteDimensional.of_finrank_eq_succ hSE
  have hEcard : Nat.card E = 4 := by
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
  have hGL : Nat.card (Module.End E S)ˣ = 3 := by
    rw [← Nat.card_congr (Units.mapEquiv eEnd.toMulEquiv).toEquiv,
      Nat.card_units, hEcard]
  let rhoE := MonoidHom.toHomUnits
    (schurSimpleActionEndRepresentation sigma S)
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
      rw [← schurSimpleActionEndRepresentation_ker sigma S,
        ← MonoidHom.ker_toHomUnits, hkerTop]
      exact Subgroup.mem_top g
    exact (hnonfixed hfixed).elim
  · exact hrange

/-- The literal row kernel has either one or three orbits in every transitive
original action. -/
theorem schurSimpleActionKernel_orbit_classes_eq_one_or_three
    [Finite B] [Finite X] [MulAction B X]
    [MulAction.IsPretransitive B X]
    [FiniteDimensional (ZMod 2) A]
    (x : X)
    (sigma : Representation (ZMod 2) B A)
    (S : Submodule (ZMod 2)[B] sigma.asModule)
    [IsSimpleModule (ZMod 2)[B] S]
    (hnonfixed : ¬ representationSubmoduleFixed sigma S)
    (hq : schurSimpleProductDegree sigma S = 2) :
    Nat.card (MulAction.orbitRel.Quotient
      (schurSimpleActionKernel sigma S) X) = 1 ∨
    Nat.card (MulAction.orbitRel.Quotient
      (schurSimpleActionKernel sigma S) X) = 3 := by
  let rhoE := MonoidHom.toHomUnits
    (schurSimpleActionEndRepresentation sigma S)
  let f : B →* rhoE.range := rhoE.rangeRestrict
  have hcard : Nat.card rhoE.range = 3 :=
    schurSimpleActionEndRepresentation_range_card_eq_three
      sigma S hnonfixed hq
  have hclasses := kernel_orbit_classes_card_eq_image_index
    (G := B) (X := X) x f (by
      simpa [f] using rhoE.rangeRestrict_surjective)
  have hdvd : ((MulAction.stabilizer B x).map f).index ∣ 3 := by
    rw [← hcard]
    exact ((MulAction.stabilizer B x).map f).index_dvd_card
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with hi | hi
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

/-- At original degree at least 24, every orbit of the scalar-row kernel has
length at least eight. -/
theorem eight_le_schurSimpleActionKernel_orbit_card
    [Finite B] [Finite X] [MulAction B X]
    [MulAction.IsPretransitive B X]
    [FiniteDimensional (ZMod 2) A]
    (x : X)
    (sigma : Representation (ZMod 2) B A)
    (S : Submodule (ZMod 2)[B] sigma.asModule)
    [IsSimpleModule (ZMod 2)[B] S]
    (hnonfixed : ¬ representationSubmoduleFixed sigma S)
    (hq : schurSimpleProductDegree sigma S = 2)
    (hs : 24 ≤ Nat.card X)
    (o : MulAction.orbitRel.Quotient
      (schurSimpleActionKernel sigma S) X) :
    8 ≤ Nat.card o.orbit := by
  let K := schurSimpleActionKernel sigma S
  have hclasses := schurSimpleActionKernel_orbit_classes_eq_one_or_three
    x sigma S hnonfixed hq
  have hprod := normal_orbit_card_mul_classes K x
  have horbit := normal_orbit_card_eq K x o
  rcases hclasses with hclasses | hclasses
  · rw [hclasses, mul_one] at hprod
    rw [horbit]
    omega
  · rw [hclasses] at hprod
    rw [horbit]
    omega

end SymmetricSubgroupAsymptotics

end
