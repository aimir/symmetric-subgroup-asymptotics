import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalPairDiagonal
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedOuterTorusAction
import SymmetricSubgroupAsymptotics.CFSGCoordinateConjugationNormalizer
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldScalarNormalizer

/-! An actual pair-preserving automorphism of the SAME original Ree
quotient has a scalar-semilinear outer root restriction. Its scalar
normalizer premise is proved using the intrinsic diagonal and literal
fixed-torus conjugations, without lifting the automorphism. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalOuterSemilinear
open CFSGReeFFourFieldParameters CFSGReeFFourOriginalPairRestriction
open CFSGReeFFourOriginalPairDiagonal CFSGReeFFourOuterTorusAction
open CFSGReeFFourFixedOuterTorusAction CFSGReeFFourPerfectProjection
open CFSGReeFFourFixedTorusGroup CFSGReeFFourFixedTorus
open CFSGReeFFourFixedDiagonalCardinality CFSGFiniteFieldScalarNormalizer
open CFSGCoordinateConjugationNormalizer

/-- A typed value wrapper prevents repeated coercion of the concrete restriction hom. -/
def outerAction (m : ℕ) (hm : 0<m) (f : pairStabilizer m hm) : AddAut (Field m) :=
  outerRestriction m hm f

theorem outerAction_apply (m : ℕ) (hm : 0<m) (f : pairStabilizer m hm) (a : Field m) :
    outerAction m hm f a=outerRestriction m hm f a := rfl

theorem outerRestriction_conjugate_scalar (m : ℕ) (hm : 0<m)
    (f : pairStabilizer m hm) (c : (Field m)ˣ) :
    ∃ r : (Field m)ˣ,outerAction m hm f*scalarHom (Field m) c*
      (outerAction m hm f)⁻¹=scalarHom (Field m) r := by
  have hsq : ∃ a : (Field m)ˣ,a^2=c := unit_square_surjective m c
  obtain ⟨a,ha⟩ := hsq
  let d := originalOuterTorus m hm a
  have hd : d∈originalDiagonal m hm := by
    rw [←fixedDiagonal_map_originalDiagonal m hm]
    exact ⟨fixedTorus m a 1,fixedTorus_mem_diagonal m a 1,rfl⟩
  have hfd : f.val d∈originalDiagonal m hm := by
    rw [←originalDiagonal_map_pair m hm f]
    exact ⟨d,hd,rfl⟩
  obtain ⟨u,v,huv⟩ := exists_originalDiagonal_torus m hm (f.val d) hfd
  refine ⟨outerScalar m u v,?_⟩
  let i : Field m → CFSG.Models.ReeF4 m :=
    fun x=>originalOuterHom m hm (Multiplicative.ofAdd x)
  have hi : Function.Injective i := by
    intro x y he
    exact congrArg Multiplicative.toAdd (originalOuterHom_injective m hm he)
  have hF (x : Field m) : i (outerAction m hm f x)=f.val (i x) :=
    outerRestriction_intertwines m hm f x
  have hR (x : Field m) : i (scalarHom (Field m) c x)=d*i x*d⁻¹ := by
    have he := original_torus_outer_action m hm a x
    have hac : (a : Field m)^2=(c : Field m) := by
      simpa only [Units.val_pow_eq_pow_val] using congrArg Units.val ha
    rw [hac] at he
    simpa only [scalarHom_apply,mul_comm] using he.symm
  have hR' (x : Field m) : i (scalarHom (Field m) (outerScalar m u v) x)=
      f.val d*i x*(f.val d)⁻¹ := by
    rw [huv]
    simpa only [scalarHom_apply,mul_comm] using
      (original_fixed_torus_outer_action m hm u v x).symm
  apply AddEquiv.ext
  intro x
  exact coordinate_conjugate_apply i hi f.val (outerAction m hm f).toEquiv
    (scalarHom (Field m) c) (scalarHom (Field m) (outerScalar m u v)) d hF hR hR' x

theorem outerRestriction_mem_scalar_normalizer (m : ℕ) (hm : 0<m)
    (f : pairStabilizer m hm) :
    outerAction m hm f∈Subgroup.normalizer (scalarSubgroup (Field m) : Set (AddAut (Field m))) := by
  have hc (g : pairStabilizer m hm) (R : AddAut (Field m))
      (hR : R∈scalarSubgroup (Field m)) :
      outerAction m hm g*R*(outerAction m hm g)⁻¹∈scalarSubgroup (Field m) := by
    obtain ⟨c,rfl⟩ := hR
    obtain ⟨r,hr⟩ := outerRestriction_conjugate_scalar m hm g c
    exact ⟨r,hr.symm⟩
  exact hom_mem_normalizer_of_conjugate_closed (outerRestriction m hm)
    (scalarSubgroup (Field m)) hc f


theorem outerRestriction_scalar_ringAut (m : ℕ) (hm : 0<m)
    (f : pairStabilizer m hm) :
    ∃! p : (Field m)ˣ×(Field m ≃+* Field m),
      ∀ x : Field m,outerAction m hm f x=(p.1 : Field m)*p.2 x :=
  exists_unique_scalar_ringAut (outerAction m hm f)
    (outerRestriction_mem_scalar_normalizer m hm f)

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalOuterSemilinear
