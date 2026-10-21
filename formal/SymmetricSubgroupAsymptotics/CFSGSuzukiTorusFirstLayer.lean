import SymmetricSubgroupAsymptotics.CFSGSuzukiFirstLayerAutomorphism
import SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotentTorusAction
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldScalarNormalizer
import Mathlib.Tactic.Group

/-! The actual Suzuki torus induces exactly all nonzero scalar maps on
its intrinsic first layer. Consequently an actual U automorphism
normalizing this literal torus induces a scalar times a field automorphism.
This is a proved layer reconstruction, not an Out-classification premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotent
open CFSGSuzukiFieldParameters CFSGSuzukiTorus CFSGFiniteFieldScalarNormalizer

def torusAut (m : ℕ) (c : (Field m)ˣ) : MulAut (unipotentSubgroup m) :=
  MulEquiv.ofBijective (torusAction m c) (by
    constructor
    · intro g h he
      apply Subtype.ext
      exact (MulAut.conj (torusElement m c)).injective (congrArg Subtype.val he)
    · intro g
      refine ⟨torusAction m c⁻¹ g,?_⟩
      apply Subtype.ext
      change torusElement m c*(torusElement m c⁻¹*g.val*(torusElement m c⁻¹)⁻¹)*
        (torusElement m c)⁻¹=g.val
      rw [←torusElement_inv m c]
      group)

def torusAutHom (m : ℕ) : (Field m)ˣ→*MulAut (unipotentSubgroup m) where
  toFun := torusAut m
  map_one' := by
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    change torusElement m 1*g.val*(torusElement m 1)⁻¹=g.val
    rw [torusElement_one]
    simp only [one_mul,inv_one,mul_one]
  map_mul' c d := by
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    change torusElement m (c*d)*g.val*(torusElement m (c*d))⁻¹=
      torusElement m c*(torusElement m d*g.val*(torusElement m d)⁻¹)*(torusElement m c)⁻¹
    rw [torusElement_mul]
    group

def firstLayerAutHom (m : ℕ) (hm : 1≤m) :
    MulAut (unipotentSubgroup m)→*AddAut (Field m) where
  toFun := firstLayerAddAut m hm
  map_one' := by
    apply AddEquiv.ext
    intro x
    have he := firstLayerAddAut_first m hm 1 (coordinateElement m x 0)
    exact he
  map_mul' f g := by
    apply AddEquiv.ext
    intro x
    have hfg := firstLayerAddAut_first m hm (f*g) (coordinateElement m x 0)
    have hg := firstLayerAddAut_first m hm g (coordinateElement m x 0)
    have hf := firstLayerAddAut_first m hm f (g (coordinateElement m x 0))
    change firstLayerAddAut m hm (f*g) x=firstParameter m (f (g (coordinateElement m x 0))) at hfg
    change firstLayerAddAut m hm g x=firstParameter m (g (coordinateElement m x 0)) at hg
    change firstLayerAddAut m hm f (firstParameter m (g (coordinateElement m x 0)))=
      firstParameter m (f (g (coordinateElement m x 0))) at hf
    change firstLayerAddAut m hm (f*g) x=
      firstLayerAddAut m hm f (firstLayerAddAut m hm g x)
    rw [hfg,hg,hf]

theorem firstLayer_torusAut (m : ℕ) (hm : 1≤m) (c : (Field m)ˣ) :
    firstLayerAutHom m hm (torusAutHom m c)=scalarHom (Field m) c⁻¹ := by
  apply AddEquiv.ext
  intro x
  have he := firstLayerAddAut_first m hm (torusAut m c) (coordinateElement m x 0)
  change firstLayerAddAut m hm (torusAut m c) x=
    firstParameter m (torusAction m c (coordinateElement m x 0)) at he
  rw [torusAction_coordinateElement,firstParameter_coordinateElement] at he
  change firstLayerAddAut m hm (torusAut m c) x=((c⁻¹ : (Field m)ˣ) : Field m)*x
  simpa only [Units.val_inv_eq_inv_val] using he

theorem firstLayer_map_torus (m : ℕ) (hm : 1≤m) :
    (torusAutHom m).range.map (firstLayerAutHom m hm)=scalarSubgroup (Field m) := by
  ext A
  constructor
  · rintro ⟨f,⟨c,rfl⟩,rfl⟩
    exact ⟨c⁻¹,(firstLayer_torusAut m hm c).symm⟩
  · rintro ⟨c,rfl⟩
    refine ⟨torusAutHom m c⁻¹,⟨c⁻¹,rfl⟩,?_⟩
    rw [firstLayer_torusAut,inv_inv]

theorem firstLayer_mem_scalar_normalizer (m : ℕ) (hm : 1≤m)
    (f : MulAut (unipotentSubgroup m))
    (hf : f∈Subgroup.normalizer ((torusAutHom m).range : Set (MulAut (unipotentSubgroup m)))) :
    firstLayerAddAut m hm f∈Subgroup.normalizer (scalarSubgroup (Field m) : Set (AddAut (Field m))) := by
  have he := Subgroup.le_normalizer_map (H:=(torusAutHom m).range) (firstLayerAutHom m hm)
    (show firstLayerAutHom m hm f∈
      (Subgroup.normalizer ((torusAutHom m).range : Set (MulAut (unipotentSubgroup m)))).map
        (firstLayerAutHom m hm) from ⟨f,hf,rfl⟩)
  rw [firstLayer_map_torus] at he
  exact he

theorem firstLayer_scalar_ringAut (m : ℕ) (hm : 1≤m)
    (f : MulAut (unipotentSubgroup m))
    (hf : f∈Subgroup.normalizer ((torusAutHom m).range : Set (MulAut (unipotentSubgroup m)))) :
    ∃! p : (Field m)ˣ×(Field m ≃+* Field m),
      ∀ g : unipotentSubgroup m,firstParameter m (f g)=(p.1 : Field m)*p.2 (firstParameter m g) := by
  obtain ⟨p,hp,hunique⟩ := exists_unique_scalar_ringAut (firstLayerAddAut m hm f)
    (firstLayer_mem_scalar_normalizer m hm f hf)
  refine ⟨p,?_,?_⟩
  · intro g
    rw [←firstLayerAddAut_first m hm f g]
    exact hp _
  · intro q hq
    apply hunique q
    intro x
    have he := hq (coordinateElement m x 0)
    rw [←firstLayerAddAut_first m hm f] at he
    exact he

end SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotent
