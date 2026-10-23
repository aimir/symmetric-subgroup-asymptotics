import SymmetricSubgroupAsymptotics.CFSGFiniteFieldScalarNormalizerCard
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldLargeSubfield
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Tactic.Group

/-! Normalizing a literal scalar subgroup which generates the SAME
field forces field-semilinearity. The closure condition is a concrete
field-generation statement, intended for the actual unitary torus
image; no abstract simple-group automorphism classification is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGFiniteFieldScalarNormalizer
variable {K : Type*} [Field K]

def normalizedAddHom (A : AddAut K) : K →+ K where
  toFun x := A x / A 1
  map_zero' := by rw [map_zero, zero_div]
  map_add' x y := by rw [map_add, add_div]

theorem normalizedAddHom_one (A : AddAut K) : normalizedAddHom A 1 = 1 :=
  div_self (additive_one_ne_zero A)

theorem normalizedAddHom_ne_zero (A : AddAut K) (a : K) (ha : a ≠ 0) :
    normalizedAddHom A a ≠ 0 := by
  apply div_ne_zero _ (additive_one_ne_zero A)
  intro he
  exact ha (A.injective (he.trans (map_zero A).symm))

def multiplicativeScalarField (A : AddAut K) : Subfield K where
  carrier := {a | ∀ x : K, normalizedAddHom A (a * x) =
    normalizedAddHom A a * normalizedAddHom A x}
  zero_mem' := by intro x; simp only [zero_mul, map_zero]
  one_mem' := by intro x; rw [one_mul, normalizedAddHom_one, one_mul]
  add_mem' := by
    intro a b ha hb x
    rw [add_mul, map_add, ha x, hb x, map_add, add_mul]
  neg_mem' := by
    intro a ha x
    rw [neg_mul, map_neg, ha x, map_neg, neg_mul]
  mul_mem' := by
    intro a b ha hb x
    rw [mul_assoc, ha (b * x), hb x, ← mul_assoc, ← ha b]
  inv_mem' := by
    intro a ha
    by_cases ha0 : a = 0
    · subst a
      intro x
      simp only [inv_zero, zero_mul, map_zero]
    · have hBa : normalizedAddHom A a ≠ 0 := normalizedAddHom_ne_zero A a ha0
      have hInv : normalizedAddHom A a⁻¹ = (normalizedAddHom A a)⁻¹ := by
        apply mul_left_cancel₀ hBa
        calc
          normalizedAddHom A a * normalizedAddHom A a⁻¹ = normalizedAddHom A (a * a⁻¹) :=
            (ha a⁻¹).symm
          _ = 1 := by rw [mul_inv_cancel₀ ha0, normalizedAddHom_one]
          _ = normalizedAddHom A a * (normalizedAddHom A a)⁻¹ := (mul_inv_cancel₀ hBa).symm
      intro x
      apply mul_left_cancel₀ hBa
      calc
        normalizedAddHom A a * normalizedAddHom A (a⁻¹ * x) =
            normalizedAddHom A (a * (a⁻¹ * x)) := (ha (a⁻¹ * x)).symm
        _ = normalizedAddHom A x := by rw [← mul_assoc, mul_inv_cancel₀ ha0, one_mul]
        _ = normalizedAddHom A a *
            (normalizedAddHom A a⁻¹ * normalizedAddHom A x) := by
          rw [hInv, ← mul_assoc, mul_inv_cancel₀ hBa, one_mul]

def scalarSubgroupOf (H : Subgroup Kˣ) : Subgroup (AddAut K) := H.map (scalarHom K)

theorem subgroup_unit_mem_multiplicativeScalarField (H : Subgroup Kˣ) (A : AddAut K)
    (hA : A ∈ Subgroup.normalizer (scalarSubgroupOf H : Set (AddAut K)))
    (u : Kˣ) (hu : u ∈ H) : (u : K) ∈ multiplicativeScalarField A := by
  have hc := (Subgroup.mem_normalizer_iff.mp hA (scalarHom K u)).mp ⟨u, hu, rfl⟩
  obtain ⟨v, hv, he⟩ := hc
  have hact (x : K) : A ((u : K) * x) = (v : K) * A x := by
    have hh := congrArg (fun f : AddAut K => f (A x)) he
    change (v : K) * A x = A ((u : K) * A.symm (A x)) at hh
    rw [A.symm_apply_apply] at hh
    exact hh.symm
  intro x
  change A ((u : K) * x) / A 1 = (A (u : K) / A 1) * (A x / A 1)
  have hunit : A (u : K) = (v : K) * A 1 := by
    simpa only [mul_one] using hact 1
  have hrel : A ((u : K) * x) * A 1 = A (u : K) * A x := by
    rw [hact x, hunit]
    ring
  field_simp [additive_one_ne_zero A]
  exact hrel

theorem scalar_relation_of_generating_subgroup (H : Subgroup Kˣ)
    (hgen : Subfield.closure ((fun u : Kˣ => (u : K)) '' (H : Set Kˣ)) = ⊤)
    (A : AddAut K) (hA : A ∈ Subgroup.normalizer (scalarSubgroupOf H : Set (AddAut K)))
    (a x : K) : A (a * x) * A 1 = A a * A x := by
  have hle : Subfield.closure ((fun u : Kˣ => (u : K)) '' (H : Set Kˣ)) ≤
      multiplicativeScalarField A := by
    apply Subfield.closure_le.mpr
    rintro _ ⟨u, hu, rfl⟩
    exact subgroup_unit_mem_multiplicativeScalarField H A hA u hu
  rw [hgen] at hle
  have ha : a ∈ multiplicativeScalarField A := hle (show a ∈ (⊤ : Subfield K) from trivial)
  have he := ha x
  change A (a * x) / A 1 = (A a / A 1) * (A x / A 1) at he
  field_simp [additive_one_ne_zero A] at he
  exact he

theorem conjugate_scalar_mem_of_generating_normalizer (H : Subgroup Kˣ)
    (hgen : Subfield.closure ((fun u : Kˣ => (u : K)) '' (H : Set Kˣ)) = ⊤)
    (A : AddAut K) (hA : A ∈ Subgroup.normalizer (scalarSubgroupOf H : Set (AddAut K)))
    (u : Kˣ) : A * scalarHom K u * A⁻¹ ∈ scalarSubgroup K := by
  have ha : A (u : K) ≠ 0 := by
    intro he
    exact Units.ne_zero u (A.injective (he.trans (map_zero A).symm))
  let v : Kˣ := Units.mk0 (A (u : K) / A 1) (div_ne_zero ha (additive_one_ne_zero A))
  refine ⟨v, ?_⟩
  apply AddEquiv.ext
  intro x
  change (A (u : K) / A 1) * x = A ((u : K) * A.symm x)
  have he := scalar_relation_of_generating_subgroup H hgen A hA (u : K) (A.symm x)
  rw [A.apply_symm_apply] at he
  calc
    (A (u : K) / A 1) * x = (A (u : K) * x) / A 1 := by ring
    _ = A ((u : K) * A.symm x) := ((eq_div_iff (additive_one_ne_zero A)).mpr he).symm

theorem generating_scalar_normalizer_le (H : Subgroup Kˣ)
    (hgen : Subfield.closure ((fun u : Kˣ => (u : K)) '' (H : Set Kˣ)) = ⊤) :
    Subgroup.normalizer (scalarSubgroupOf H : Set (AddAut K)) ≤
      Subgroup.normalizer (scalarSubgroup K : Set (AddAut K)) := by
  intro A hA
  apply Subgroup.mem_normalizer_iff.mpr
  intro B
  constructor
  · rintro ⟨u, rfl⟩
    exact conjugate_scalar_mem_of_generating_normalizer H hgen A hA u
  · intro hB
    have he : A⁻¹ * (A * B * A⁻¹) * (A⁻¹)⁻¹ ∈ scalarSubgroup K := by
      obtain ⟨u, hu⟩ := hB
      rw [← hu]
      exact conjugate_scalar_mem_of_generating_normalizer H hgen A⁻¹
        ((Subgroup.normalizer _).inv_mem hA) u
    have hc : A⁻¹ * (A * B * A⁻¹) * (A⁻¹)⁻¹ = B := by group
    rwa [hc] at he

theorem card_generating_scalarNormalizer_le [Finite K] (H : Subgroup Kˣ)
    (hgen : Subfield.closure ((fun u : Kˣ => (u : K)) '' (H : Set Kˣ)) = ⊤) :
    Nat.card (Subgroup.normalizer (scalarSubgroupOf H : Set (AddAut K))) ≤
      Nat.card Kˣ * Nat.card (K ≃+* K) := by
  let f : Subgroup.normalizer (scalarSubgroupOf H : Set (AddAut K)) →
      Subgroup.normalizer (scalarSubgroup K : Set (AddAut K)) :=
    fun A => ⟨A.val, generating_scalar_normalizer_le H hgen A.property⟩
  have hf : Function.Injective f := by
    intro A B he
    have hv : A.val = B.val := congrArg
      (fun C : Subgroup.normalizer (scalarSubgroup K : Set (AddAut K)) => C.val) he
    exact Subtype.ext hv
  exact (Nat.card_le_card_of_injective f hf).trans (card_scalarNormalizer_le K)

theorem large_scalar_normalizer_le [Finite K] (H : Subgroup Kˣ)
    (hlarge : Nat.card K < Nat.card H ^ 2) :
    Subgroup.normalizer (scalarSubgroupOf H : Set (AddAut K)) ≤
      Subgroup.normalizer (scalarSubgroup K : Set (AddAut K)) :=
  generating_scalar_normalizer_le H
    (CFSGFiniteFieldLargeSubfield.closure_unit_subgroup_eq_top H hlarge)

theorem exists_unique_scalar_ringAut_of_large [Finite K] (H : Subgroup Kˣ)
    (hlarge : Nat.card K < Nat.card H ^ 2) (A : AddAut K)
    (hA : A ∈ Subgroup.normalizer (scalarSubgroupOf H : Set (AddAut K))) :
    ∃! p : Kˣ × (K ≃+* K), ∀ x : K, A x = (p.1 : K) * p.2 x :=
  exists_unique_scalar_ringAut A (large_scalar_normalizer_le H hlarge hA)

theorem card_large_scalarNormalizer_le [Finite K] (H : Subgroup Kˣ)
    (hlarge : Nat.card K < Nat.card H ^ 2) :
    Nat.card (Subgroup.normalizer (scalarSubgroupOf H : Set (AddAut K))) ≤
      Nat.card Kˣ * Nat.card (K ≃+* K) :=
  card_generating_scalarNormalizer_le H
    (CFSGFiniteFieldLargeSubfield.closure_unit_subgroup_eq_top H hlarge)

end SymmetricSubgroupAsymptotics.CFSGFiniteFieldScalarNormalizer
