import SymmetricSubgroupAsymptotics.CFSGSuzukiTorusFirstLayer
import SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotentAutomorphismRigidity

/-! The first-layer action is faithful on the actual normalizer of the
Suzuki torus action in Aut(U). A first-trivial normalizer element must
centralize the torus, since the latter acts faithfully on the first layer;
the proved intrinsic rigidity then eliminates it. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotent
open CFSGSuzukiFieldParameters CFSGFiniteFieldScalarNormalizer

theorem torusAutHom_injective (m : ℕ) (hm : 1≤m) : Function.Injective (torusAutHom m) := by
  intro c d he
  have hh := congrArg (firstLayerAutHom m hm) he
  rw [firstLayer_torusAut,firstLayer_torusAut] at hh
  exact inv_injective (scalarHom_injective (Field m) hh)

theorem firstLayer_injective_on_torus (m : ℕ) (hm : 1≤m)
    {f g : MulAut (unipotentSubgroup m)}
    (hf : f∈(torusAutHom m).range) (hg : g∈(torusAutHom m).range)
    (he : firstLayerAutHom m hm f=firstLayerAutHom m hm g) : f=g := by
  obtain ⟨c,rfl⟩ := hf
  obtain ⟨d,rfl⟩ := hg
  rw [firstLayer_torusAut,firstLayer_torusAut] at he
  exact congrArg (torusAutHom m) (inv_injective (scalarHom_injective (Field m) he))

theorem normalizer_first_kernel (m : ℕ) (hm : 1≤m)
    (f : MulAut (unipotentSubgroup m))
    (hf : f∈Subgroup.normalizer ((torusAutHom m).range : Set (MulAut (unipotentSubgroup m))))
    (hfirst : firstLayerAutHom m hm f=1) : f=1 := by
  have hcentral : ∀ c : (Field m)ˣ,f*torusAutHom m c*f⁻¹=torusAutHom m c := by
    intro c
    have hc : f*torusAutHom m c*f⁻¹∈(torusAutHom m).range :=
      (Subgroup.mem_normalizer_iff.mp hf (torusAutHom m c)).mp ⟨c,rfl⟩
    apply firstLayer_injective_on_torus m hm hc ⟨c,rfl⟩
    rw [map_mul,map_mul,map_inv,hfirst]
    simp only [one_mul,inv_one,mul_one]
  have hfix : ∀ g : unipotentSubgroup m,firstParameter m (f g)=firstParameter m g := by
    intro g
    have he := firstLayerAddAut_first m hm f g
    change firstLayerAutHom m hm f (firstParameter m g)=firstParameter m (f g) at he
    rw [hfirst] at he
    exact he.symm
  have hcomm : ∀ (c : (Field m)ˣ) (g : unipotentSubgroup m),
      f (torusAction m c g)=torusAction m c (f g) := by
    intro c g
    have he := congrArg (fun A : MulAut (unipotentSubgroup m) => A (f g)) (hcentral c)
    change f (torusAction m c (f.symm (f g)))=torusAction m c (f g) at he
    rw [f.symm_apply_apply] at he
    exact he
  apply MulEquiv.ext
  intro g
  exact congrArg (fun h : unipotentSubgroup m→*unipotentSubgroup m => h g)
    (endomorphism_eq_id_of_first_and_torus m hm f.toMonoidHom hfix hcomm)

def normalizerFirstHom (m : ℕ) (hm : 1≤m) :
    (Subgroup.normalizer ((torusAutHom m).range : Set (MulAut (unipotentSubgroup m))))→*
      AddAut (Field m) :=
  (firstLayerAutHom m hm).comp
    (Subgroup.normalizer ((torusAutHom m).range : Set (MulAut (unipotentSubgroup m)))).subtype

theorem normalizerFirstHom_injective (m : ℕ) (hm : 1≤m) :
    Function.Injective (normalizerFirstHom m hm) := by
  apply (MonoidHom.ker_eq_bot_iff (normalizerFirstHom m hm)).mp
  apply bot_unique
  intro f hf
  apply (Subgroup.mem_bot).mpr
  apply Subtype.ext
  exact normalizer_first_kernel m hm f.val f.property hf

end SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotent
