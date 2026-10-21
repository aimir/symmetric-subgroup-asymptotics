import SymmetricSubgroupAsymptotics.CFSGSuzukiPairRestriction
import SymmetricSubgroupAsymptotics.CFSGSuzukiTorusNormalizerCard

/-! The faithful restriction of the actual opposite-pair stabilizer lies
in the actual intrinsic torus normalizer. Torus parameters are transported
through their proved original/normalized charts, not through group orders. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiPairRestriction
open CFSGSuzukiFieldParameters CFSGSuzukiTorus CFSGSuzukiUnipotent
open CFSGSuzukiSylowOfNormalizer CFSGSuzukiGoodSylow CFSGSuzukiBorelIntersection
open CFSGSuzukiAlignedAutomorphisms

def modelOriginalTorus (m : ℕ) (c : (Field m)ˣ) : ActualGroup m :=
  ⟨torusElement m c,torusElement_mem_model m c⟩

theorem modelOriginalTorus_mem (m : ℕ) (c : (Field m)ˣ) :
    modelOriginalTorus m c∈modelTorus m := by
  obtain ⟨d,hd⟩ := original_torus_eq_normalized m c
  exact ⟨d,hd.symm⟩

theorem modelTorus_original_parameter (m : ℕ) (t : ActualGroup m) (ht : t∈modelTorus m) :
    ∃ c : (Field m)ˣ,t.val=torusElement m c := by
  obtain ⟨d,hd⟩ := ht
  let c : (Field m)ˣ := Units.mk0 (inverseTorusParameter m (d : Field m))
    (div_ne_zero (pow_ne_zero 2 (Units.ne_zero d)) (theta_ne_zero m (Units.ne_zero d)))
  exact ⟨c,hd.symm⟩

theorem pairRestriction_conjugate_torus (m : ℕ) (f : pairStabilizer m) (c : (Field m)ˣ) :
    ∃ d : (Field m)ˣ,pairRestriction m f*torusAutHom m c*(pairRestriction m f)⁻¹=torusAutHom m d := by
  let t := modelOriginalTorus m c
  have ht : t∈modelTorus m := modelOriginalTorus_mem m c
  have hT := map_torus_of_fix_opposite_pair m f.val f.property.1 f.property.2
  have hft : f.val t∈modelTorus m := by
    rw [←hT]
    exact ⟨t,ht,rfl⟩
  obtain ⟨d,hd⟩ := modelTorus_original_parameter m (f.val t) hft
  refine ⟨d,?_⟩
  apply MulEquiv.ext
  intro u
  apply Subtype.ext
  let g : ActualGroup m := ⟨u.val,unipotentSubgroup_le_model m u.property⟩
  change (f.val (t*f.val.symm g*t⁻¹)).val=torusElement m d*u.val*(torusElement m d)⁻¹
  rw [map_mul,map_mul,map_inv,f.val.apply_symm_apply]
  change (f.val t).val*u.val*((f.val t).val)⁻¹=torusElement m d*u.val*(torusElement m d)⁻¹
  rw [hd]

theorem pairRestriction_mem_torus_normalizer (m : ℕ) (f : pairStabilizer m) :
    pairRestriction m f∈Subgroup.normalizer ((torusAutHom m).range : Set (MulAut (unipotentSubgroup m))) := by
  have hforward : ∀ (a : pairStabilizer m) (A : MulAut (unipotentSubgroup m)),
      A∈(torusAutHom m).range→pairRestriction m a*A*(pairRestriction m a)⁻¹∈(torusAutHom m).range := by
    rintro a A ⟨c,rfl⟩
    obtain ⟨d,hd⟩ := pairRestriction_conjugate_torus m a c
    exact ⟨d,hd.symm⟩
  apply Subgroup.mem_normalizer_iff.mpr
  intro A
  constructor
  · exact hforward f A
  · intro hA
    have he := hforward f⁻¹ _ hA
    have hc : pairRestriction m f⁻¹*(pairRestriction m f*A*(pairRestriction m f)⁻¹)*
        (pairRestriction m f⁻¹)⁻¹=A := by
      rw [map_inv]
      group
    rwa [hc] at he

def pairNormalizerMap (m : ℕ) : pairStabilizer m→
    Subgroup.normalizer ((torusAutHom m).range : Set (MulAut (unipotentSubgroup m))) :=
  fun f => ⟨pairRestriction m f,pairRestriction_mem_torus_normalizer m f⟩

theorem pairNormalizerMap_injective (m : ℕ) : Function.Injective (pairNormalizerMap m) := by
  intro f g he
  exact pairRestriction_injective m (congrArg Subtype.val he)

theorem pairStabilizer_card_le (m : ℕ) (hm : 1≤m) :
    Nat.card (pairStabilizer m)≤(2^(2*m+1)-1)*(2*m+1) :=
  (Nat.card_le_card_of_injective (pairNormalizerMap m) (pairNormalizerMap_injective m)).trans
    (card_torus_normalizer_le m hm)

end SymmetricSubgroupAsymptotics.CFSGSuzukiPairRestriction
