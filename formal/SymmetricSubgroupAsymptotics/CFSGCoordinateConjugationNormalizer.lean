import Mathlib.GroupTheory.GroupAction.ConjAct

/-! Coordinate conjugation and a group-valued normalizer criterion.
The coordinate map need only be an injective function, so the same
statement applies to additive and nonabelian root-group coordinates. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGCoordinateConjugationNormalizer

theorem coordinate_conjugate_apply {C G : Type*} [Group G]
    (i : C → G) (hi : Function.Injective i) (f : MulAut G) (F : C ≃ C)
    (R R' : C → C) (d : G)
    (hF : ∀ x,i (F x)=f (i x))
    (hR : ∀ x,i (R x)=d*i x*d⁻¹)
    (hR' : ∀ x,i (R' x)=f d*i x*(f d)⁻¹) (x : C) :
    F (R (F.symm x))=R' x := by
  apply hi
  calc
    _=f (i (R (F.symm x))) := hF _
    _=f (d*i (F.symm x)*d⁻¹) := congrArg f (hR _)
    _=f d*i x*(f d)⁻¹ := by
      rw [map_mul,map_mul,map_inv,←hF,F.apply_symm_apply]
    _=i (R' x) := (hR' x).symm

theorem hom_mem_normalizer_of_conjugate_closed {P G : Type*} [Group P] [Group G]
    (h : P →* G) (L : Subgroup G)
    (hc : ∀ a : P,∀ x∈L,h a*x*(h a)⁻¹∈L) (a : P) :
    h a∈Subgroup.normalizer (L : Set G) := by
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  constructor
  · exact hc a x
  · intro hx
    have he := hc a⁻¹ _ hx
    rw [map_inv] at he
    have hcancel : (h a)⁻¹*(h a*x*(h a)⁻¹)*((h a)⁻¹)⁻¹=x := by
      simp [mul_assoc]
    rwa [hcancel] at he

end SymmetricSubgroupAsymptotics.CFSGCoordinateConjugationNormalizer
