import SymmetricSubgroupAsymptotics.CFSGReeGTwoPairRestriction
import SymmetricSubgroupAsymptotics.CFSGReeGTwoAlignedAutomorphisms
import SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveAutomorphismLayers
import SymmetricSubgroupAsymptotics.CFSGReeGTwoPermutationDegree
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldSquareScalarNormalizerCard

/-! The actual opposed-pair stabilizer acts on the literal central
field axis. Squared torus elements are preserved as a family, so this
additive action belongs to the proved square-scalar normalizer. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoAlignedCentreAction
open CFSGReeGTwoFieldParameters CFSGReeGTwoFixedModelEquivalence
open CFSGReeGTwoPairRestriction CFSGReeGTwoPositiveCentre
open CFSGReeGTwoPositiveAutomorphismLayers CFSGReeGTwoPermutationDegree
open CFSGReeGTwoDerivedPairNormalizer CFSGReeGTwoAlignedAutomorphisms
open CFSGReeGTwoOriginalTorus CFSGFiniteFieldScalarNormalizer

private theorem scalar_relation_of_conjugation {K G : Type*} [Field K] [Group G]
    (z : Multiplicative K→*G) (hz : Function.Injective z) (F : MulAut G) (A : AddAut K)
    (hZ : ∀d,F (z (Multiplicative.ofAdd d))=z (Multiplicative.ofAdd (A d)))
    (r s : G) (a b : K)
    (hr : ∀d,r*z (Multiplicative.ofAdd d)*r⁻¹=z (Multiplicative.ofAdd (d*a)))
    (hs : ∀d,s*z (Multiplicative.ofAdd d)*s⁻¹=z (Multiplicative.ofAdd (d*b)))
    (hF : F r=s) (d : K) : A (d*a)=A d*b := by
  have hh := congrArg F (hr d)
  rw [map_mul,map_mul,map_inv,hF,hZ,hZ,hs] at hh
  exact congrArg Multiplicative.toAdd (hz hh.symm)

def alignedCentreAction (m : ℕ) (hm : 1≤m) : pairStabilizer m hm→*AddAut (Field m) :=
  (centralAction m).comp (pairRestriction m hm)

theorem pair_central_intertwine (m : ℕ) (hm : 1≤m) (f : pairStabilizer m hm) (d : Field m) :
    f.val (centralDerivedHom m hm (Multiplicative.ofAdd d))=
      centralDerivedHom m hm (Multiplicative.ofAdd (alignedCentreAction m hm f d)) := by
  apply Subtype.ext
  change (f.val ⟨(centralHom m (Multiplicative.ofAdd d)).val,_⟩).val=
    (centralHom m (Multiplicative.ofAdd (alignedCentreAction m hm f d))).val
  rw [←pairRestriction_val]
  exact congrArg (fun u:CFSGReeGTwoOriginalPositiveSubgroup.fixedPositiveGroup m=>u.val)
    (centralAction_intertwine m (pairRestriction m hm f) d)

private theorem square_is_fourth (m : ℕ) (r : (Field m)ˣ) :
    ∃s : (Field m)ˣ,r^2=(s^2)^2 := by
  obtain ⟨s,hs⟩ := CFSGFiniteFieldSignedSquares.eq_square_or_neg_square
    (Field m) (field_card_mod_four m) (r:Field m) r.ne_zero
  refine ⟨s,?_⟩
  apply Units.ext
  rcases hs with hs | hs <;>
    simp only [Units.val_pow_eq_pow_val,hs,neg_sq]

theorem pair_maps_square_torus (m : ℕ) (hm : 1≤m) (f : pairStabilizer m hm) (r : (Field m)ˣ) :
    ∃v : (Field m)ˣ,f.val (squareTorusDerived m r)=squareTorusDerived m v := by
  obtain ⟨s,hs⟩ := square_is_fourth m r
  have hT := map_torus_of_fix_opposite_pair m hm f.val
    (pair_preserves_positive m hm f) (pair_preserves_opposite m hm f)
  have hsT : squareTorusDerived m s∈derivedTorus m := ⟨s^2,rfl⟩
  have hmem : f.val (squareTorusDerived m s)∈derivedTorus m := by
    rw [←hT]
    exact ⟨squareTorusDerived m s,hsT,rfl⟩
  change (f.val (squareTorusDerived m s)).val∈(fixedTorusHom m).range at hmem
  obtain ⟨v,hv⟩ := hmem
  have hsr : squareTorusDerived m r=(squareTorusDerived m s)^2 := by
    apply Subtype.ext
    change fixedTorusHom m (r^2)=(fixedTorusHom m (s^2))^2
    rw [←map_pow,hs]
  refine ⟨v,?_⟩
  rw [hsr,map_pow]
  apply Subtype.ext
  change ((f.val (squareTorusDerived m s)).val)^2=fixedTorusHom m (v^2)
  rw [←hv,←map_pow]

private theorem centre_conjugate_square_mem (m : ℕ) (hm : 1≤m) (f : pairStabilizer m hm)
    (r : (Field m)ˣ) :
    alignedCentreAction m hm f*squareScalarHom (Field m) r*(alignedCentreAction m hm f)⁻¹∈
      squareScalarSubgroup (Field m) := by
  obtain ⟨v,hv⟩ := pair_maps_square_torus m hm f r
  let A : AddAut (Field m) := alignedCentreAction m hm f
  have hrel := scalar_relation_of_conjugation
    (centralDerivedHom m hm) (centralDerivedHom_injective m hm) f.val A
    (pair_central_intertwine m hm f)
    (squareTorusDerived m r) (squareTorusDerived m v) ((r:Field m)^2) ((v:Field m)^2)
    (squareTorusDerived_action m hm r) (squareTorusDerived_action m hm v) hv
  refine ⟨v,?_⟩
  apply AddEquiv.ext
  intro x
  change (v:Field m)^2*x=A ((r:Field m)^2*A.symm x)
  calc
    _ = x*(v:Field m)^2 := mul_comm _ _
    _ = A (A.symm x*(r:Field m)^2) := by
      have h := hrel (A.symm x)
      rw [A.apply_symm_apply] at h
      exact h.symm
    _ = A ((r:Field m)^2*A.symm x) := congrArg A (mul_comm _ _)

theorem alignedCentreAction_mem_square_normalizer (m : ℕ) (hm : 1≤m)
    (f : pairStabilizer m hm) : alignedCentreAction m hm f∈
      Subgroup.normalizer (squareScalarSubgroup (Field m):Set (AddAut (Field m))) := by
  have hforward : ∀(g : pairStabilizer m hm) (C : AddAut (Field m)),
      C∈squareScalarSubgroup (Field m)→
      alignedCentreAction m hm g*C*(alignedCentreAction m hm g)⁻¹∈squareScalarSubgroup (Field m) := by
    rintro g C ⟨r,rfl⟩
    exact centre_conjugate_square_mem m hm g r
  apply Subgroup.mem_normalizer_iff.mpr
  intro C
  constructor
  · exact hforward f C
  · intro hC
    have he := hforward f⁻¹ _ hC
    rw [map_inv] at he
    have hid : (alignedCentreAction m hm f)⁻¹*
        (alignedCentreAction m hm f*C*(alignedCentreAction m hm f)⁻¹)*
        ((alignedCentreAction m hm f)⁻¹)⁻¹=C := by group
    rwa [hid] at he

def alignedCentreNormalizerHom (m : ℕ) (hm : 1≤m) : pairStabilizer m hm→*
    Subgroup.normalizer (squareScalarSubgroup (Field m):Set (AddAut (Field m))) :=
  (alignedCentreAction m hm).codRestrict _ (alignedCentreAction_mem_square_normalizer m hm)

end SymmetricSubgroupAsymptotics.CFSGReeGTwoAlignedCentreAction
