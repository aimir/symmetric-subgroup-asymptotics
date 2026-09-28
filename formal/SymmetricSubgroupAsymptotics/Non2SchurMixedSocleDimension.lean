import SymmetricSubgroupAsymptotics.Non2SchurActionKernel
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The literal dimension of the mixed Schur socle

The numerical row profile uses `t + h * m`.  Here that number is identified
with the dimension of the actual sum of the invariant row and the complete
selected isotypic socle component.  The key point is that a nonfixed simple
module cannot contain a nonzero vector fixed by the whole acting group.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

universe u
variable {k B A : Type u} [Field k] [Group B]
    [AddCommGroup A] [Module k A]

/-- `ofModule'` followed by `asModule` carries the original group-algebra
module structure.  This explicit identity equivalence avoids changing the
module instance when applying simplicity. -/
def representationOfModulePrimeAsModuleEquiv
    (M : Type u) [AddCommGroup M] [Module k M] [Module k[B] M]
    [IsScalarTower k k[B] M] :
    (Representation.ofModule' (k := k) (G := B) M).asModule ≃ₗ[k[B]] M where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    simp only [RingHom.id_apply]
    change (Representation.ofModule' (k := k) (G := B) M).asModuleEquiv (r • x) =
      r • (Representation.ofModule' (k := k) (G := B) M).asModuleEquiv x
    rw [Representation.asModuleEquiv_map_smul]
    simp [Representation.asAlgebraHom_def, Representation.ofModule']

/-- A single nonzero vector fixed by the whole group forces a simple row to
be the fixed row. -/
theorem representationSubmoduleFixed_of_exists_ne_zero_fixed
    (sigma : Representation k B A)
    (S : Submodule k[B] sigma.asModule)
    [IsSimpleModule k[B] S]
    (x : S) (hx0 : x ≠ 0)
    (hx : ∀ g : B, MonoidAlgebra.single g (1 : k) • x = x) :
    representationSubmoduleFixed sigma S := by
  let rhoS : Representation k B S := Representation.ofModule' S
  let f : (Representation.trivial k B k).IntertwiningMap rhoS :=
    (LinearMap.toSpanSingleton k S x).intertwiningMap_of_isIntertwiningMap
      _ _ (by
        intro g c
        simp only [Representation.trivial_apply,
          LinearMap.toSpanSingleton_apply, map_smul]
        congr 1
        symm
        change MonoidAlgebra.single g (1 : k) • x = x
        exact hx g)
  let fR : (Representation.trivial k B k).asModule →ₗ[k[B]] S :=
    (representationOfModulePrimeAsModuleEquiv (k := k) (B := B) S).toLinearMap.comp
      ((Representation.IntertwiningMap.equivLinearMapAsModule
        (ρ := Representation.trivial k B k) (σ := rhoS)) f)
  have hf0 : fR ≠ 0 := by
    intro hf
    have h := LinearMap.congr_fun hf (1 : k)
    have hfone : fR (1 : k) = x := by
      change (LinearMap.toSpanSingleton k S x) 1 = x
      simp
    exact hx0 (hfone.symm.trans h)
  have hsurj : Function.Surjective fR := by
    exact LinearMap.surjective_of_ne_zero hf0
  intro g y
  obtain ⟨c, rfl⟩ := hsurj y
  calc
    MonoidAlgebra.single g (1 : k) • fR c =
        fR (MonoidAlgebra.single g (1 : k) • c) :=
      (fR.map_smul (MonoidAlgebra.single g (1 : k)) c).symm
    _ = fR c := by
      congr 1
      apply (Representation.trivial k B k).asModuleEquiv.injective
      simp only [Representation.asModuleEquiv_map_smul,
        Representation.asAlgebraHom_single, one_smul,
        Representation.trivial_apply]

/-- No nonzero vector in a nonfixed isotypic socle component is fixed by
the whole original group. -/
theorem isotypicComponent_fixed_eq_zero_of_nonfixed
    [FiniteDimensional k A]
    (sigma : Representation k B A)
    (S : Submodule k[B] sigma.asModule)
    [IsSimpleModule k[B] S]
    (hnonfixed : ¬ representationSubmoduleFixed sigma S)
    (x : isotypicComponent k[B] sigma.asModule S)
    (hx : ∀ g : B, MonoidAlgebra.single g (1 : k) • x = x) :
    x = 0 := by
  classical
  by_contra hx0
  let e := schurSocleDecomposition
    (k := k) (R := k[B]) (A := sigma.asModule) (X := S)
  have hex0 : e x ≠ 0 := by
    intro he
    apply hx0
    apply e.injective
    simpa using he
  have hnotall : ¬ ∀ i, e x i = 0 := by
    intro hall
    apply hex0
    funext i
    exact hall i
  obtain ⟨i, hi⟩ := not_forall.mp hnotall
  have hcoord (g : B) :
      MonoidAlgebra.single g (1 : k) • e x i = e x i := by
    change (MonoidAlgebra.single g (1 : k) • e x) i = e x i
    rw [← e.map_smul, hx g]
  exact hnonfixed
    (representationSubmoduleFixed_of_exists_ne_zero_fixed
      sigma S (e x i) hi hcoord)

/-- The literal invariant row is disjoint from every nonfixed simple
isotypic socle component. -/
theorem mapped_invariants_disjoint_isotypic_of_nonfixed
    [FiniteDimensional k A]
    (sigma : Representation k B A)
    (S : Submodule k[B] sigma.asModule)
    [IsSimpleModule k[B] S]
    (hnonfixed : ¬ representationSubmoduleFixed sigma S) :
    Disjoint
      (sigma.invariants.map sigma.asModuleEquiv.symm.toLinearMap)
      ((isotypicComponent k[B] sigma.asModule S).restrictScalars k) := by
  rw [disjoint_iff_inf_le]
  intro y hy
  rw [Submodule.mem_bot]
  obtain ⟨a, ha, hay⟩ := hy.1
  have hyfixed (g : B) :
      MonoidAlgebra.single g (1 : k) •
          (⟨y, hy.2⟩ : isotypicComponent k[B] sigma.asModule S) =
        ⟨y, hy.2⟩ := by
    apply Subtype.ext
    change MonoidAlgebra.single g (1 : k) • y = y
    rw [← hay, Representation.single_smul, one_smul]
    change sigma g a = a
    exact ha g
  have hz := isotypicComponent_fixed_eq_zero_of_nonfixed
    sigma S hnonfixed ⟨y, hy.2⟩ hyfixed
  exact congrArg Subtype.val hz

/-- The complete selected isotypic component has the expected dimension:
the simple dimension times its actual socle multiplicity. -/
theorem schur_isotypic_finrank_eq
    [FiniteDimensional k A]
    (sigma : Representation k B A)
    (S : Submodule k[B] sigma.asModule)
    [IsSimpleModule k[B] S] :
    Module.finrank k
        ((isotypicComponent k[B] sigma.asModule S).restrictScalars k) =
    Module.finrank k S *
        schurSocleMultiplicity (k := k) (R := k[B])
          (A := sigma.asModule) (X := S) := by
  letI : FiniteDimensional k S := FiniteDimensional.of_injective
    (S.subtype.restrictScalars k) S.subtype_injective
  let e := schurSocleDecomposition
    (k := k) (R := k[B]) (A := sigma.asModule) (X := S)
  have he0 := ((Submodule.restrictScalarsEquiv
    (R := k[B]) (M := sigma.asModule) k
      (isotypicComponent k[B] sigma.asModule S)).restrictScalars k).finrank_eq
  have he1 := (e.restrictScalars k).finrank_eq
  have he := he0.trans he1
  simpa [Module.finrank_pi_fintype, Nat.mul_comm] using he

/-- The formal number `t + h*m` is the dimension of the literal mixed
invariant/isotypic carrier when `t` is the invariant dimension. -/
theorem schurMixedSocleSubspace_finrank_eq
    [FiniteDimensional k A]
    (sigma : Representation k B A)
    (S : Submodule k[B] sigma.asModule)
    [IsSimpleModule k[B] S]
    (hnonfixed : ¬ representationSubmoduleFixed sigma S) :
    Module.finrank k (schurMixedSocleSubspace sigma S) =
      schurMixedSocleDimension sigma S
        (Module.finrank k sigma.invariants) := by
  let P := sigma.invariants.map sigma.asModuleEquiv.symm.toLinearMap
  let Q := (isotypicComponent k[B] sigma.asModule S).restrictScalars k
  have hdisjoint : Disjoint P Q :=
    mapped_invariants_disjoint_isotypic_of_nonfixed sigma S hnonfixed
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq P Q
  have hP : Module.finrank k P = Module.finrank k sigma.invariants := by
    exact sigma.asModuleEquiv.symm.finrank_map_eq sigma.invariants
  have hQ : Module.finrank k Q = Module.finrank k S *
      schurSocleMultiplicity (k := k) (R := k[B])
        (A := sigma.asModule) (X := S) :=
    schur_isotypic_finrank_eq sigma S
  rw [hdisjoint.eq_bot, finrank_bot, add_zero, hP, hQ] at hsum
  simpa [schurMixedSocleSubspace, schurMixedSocleDimension, P, Q] using hsum

/-- Any ambient dimension bound supplies the physical-size hypothesis in
the four-branch row theorem. -/
theorem schurMixedSocleDimension_le_of_finrank_le
    [FiniteDimensional k A]
    (sigma : Representation k B A)
    (S : Submodule k[B] sigma.asModule)
    [IsSimpleModule k[B] S]
    (hnonfixed : ¬ representationSubmoduleFixed sigma S)
    (s t : Nat) (ht : t = Module.finrank k sigma.invariants)
    (hA : Module.finrank k A ≤ s) :
    schurMixedSocleDimension sigma S t ≤ s := by
  subst t
  rw [← schurMixedSocleSubspace_finrank_eq sigma S hnonfixed]
  exact (Submodule.finrank_le (schurMixedSocleSubspace sigma S)).trans hA

end SymmetricSubgroupAsymptotics

end
