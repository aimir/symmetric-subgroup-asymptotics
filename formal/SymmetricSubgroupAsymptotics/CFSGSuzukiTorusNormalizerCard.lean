import SymmetricSubgroupAsymptotics.CFSGSuzukiTorusNormalizerFaithful
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldScalarNormalizerCard

/-! The actual torus normalizer inside Aut(U) has order at most
(q-1)(2m+1). Faithfulness comes from the original root-group rigidity,
and the field factor is the exact literal finite-field automorphism group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotent
open CFSGSuzukiFieldParameters CFSGFiniteFieldScalarNormalizer

def normalizerScalarMap (m : ℕ) (hm : 1≤m)
    (f : Subgroup.normalizer ((torusAutHom m).range : Set (MulAut (unipotentSubgroup m)))) :
    Subgroup.normalizer (scalarSubgroup (Field m) : Set (AddAut (Field m))) :=
  ⟨firstLayerAddAut m hm f.val,firstLayer_mem_scalar_normalizer m hm f.val f.property⟩

theorem normalizerScalarMap_injective (m : ℕ) (hm : 1≤m) :
    Function.Injective (normalizerScalarMap m hm) := by
  intro f g he
  apply normalizerFirstHom_injective m hm
  exact congrArg Subtype.val he

theorem card_torus_normalizer_le (m : ℕ) (hm : 1≤m) :
    Nat.card (Subgroup.normalizer ((torusAutHom m).range : Set (MulAut (unipotentSubgroup m))))≤
      (2^(2*m+1)-1)*(2*m+1) := by
  have hmap := Nat.card_le_card_of_injective (normalizerScalarMap m hm)
    (normalizerScalarMap_injective m hm)
  have hbound := card_scalarNormalizer_le (Field m)
  have hcard : Nat.card ((Field m)ˣ)=2^(2*m+1)-1 := by rw [Nat.card_units,field_card]
  have haut : Nat.card (Field m ≃+* Field m)=2*m+1 :=
    CFSGFiniteFieldAutomorphisms.card_galoisField_ringAut 2 (2*m+1) (by omega)
  exact hmap.trans (by simpa only [hcard,haut] using hbound)

end SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotent
