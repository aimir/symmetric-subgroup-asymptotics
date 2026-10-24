import SymmetricSubgroupAsymptotics.CFSGSuzukiFieldAutomorphisms
import SymmetricSubgroupAsymptotics.CFSGSuzukiTorusNormalizerFaithful
import SymmetricSubgroupAsymptotics.CFSGCoordinateConjugationNormalizer

/-! Actual field actions on the literal Suzuki unipotent group. The
torus normalizer's proved first-layer faithfulness upgrades a prescribed
field action on the first coordinate to its action on both coordinates.
No whole rank-one recognition or new faithfulness premise is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotentFieldActions
open CFSGSuzukiFieldParameters CFSGSuzukiUnipotent
open CFSGSuzukiFieldAutomorphisms CFSGCoordinateConjugationNormalizer

private theorem ambient_mem_unipotent (m : ℕ) (sigma : Field m ≃+* Field m)
    (g : CFSGSuzukiTorus.Ambient m) (hg : g ∈ unipotentSubgroup m) :
    ambientAut m sigma g ∈ unipotentSubgroup m := by
  obtain ⟨a,b,rfl⟩ := hg
  rw [ambientAut_unipotent]
  exact ⟨sigma a,sigma b,rfl⟩

def fieldAut (m : ℕ) (sigma : Field m ≃+* Field m) :
    MulAut (unipotentSubgroup m) where
  toFun g := ⟨ambientAut m sigma g.val,ambient_mem_unipotent m sigma g.val g.property⟩
  invFun g := ⟨ambientAut m sigma.symm g.val,
    ambient_mem_unipotent m sigma.symm g.val g.property⟩
  left_inv g := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    exact sigma.symm_apply_apply _
  right_inv g := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    exact sigma.apply_symm_apply _
  map_mul' g h := Subtype.ext (map_mul (ambientAut m sigma) g.val h.val)

theorem fieldAut_coordinate (m : ℕ) (sigma : Field m ≃+* Field m) (a b : Field m) :
    fieldAut m sigma (coordinateElement m a b) = coordinateElement m (sigma a) (sigma b) :=
  Subtype.ext (ambientAut_unipotent m sigma a b)

theorem fieldAut_first (m : ℕ) (sigma : Field m ≃+* Field m) (x : unipotentSubgroup m) :
    firstParameter m (fieldAut m sigma x) = sigma (firstParameter m x) := by
  obtain ⟨a,b,hx⟩ := x.property
  have he : x = coordinateElement m a b := Subtype.ext hx
  rw [he,fieldAut_coordinate]
  rfl

def fieldAutHom (m : ℕ) : (Field m ≃+* Field m) →* MulAut (unipotentSubgroup m) where
  toFun := fieldAut m
  map_one' := by
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    apply Units.ext
    ext i j
    rfl
  map_mul' sigma tau := by
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    apply Units.ext
    ext i j
    rfl

theorem fieldAut_torus_intertwines (m : ℕ) (sigma : Field m ≃+* Field m)
    (c : (Field m)ˣ) (x : unipotentSubgroup m) :
    fieldAut m sigma (torusAutHom m c x) =
      torusAutHom m (Units.map sigma.toMonoidHom c) (fieldAut m sigma x) := by
  obtain ⟨a,b,hx⟩ := x.property
  have he : x = coordinateElement m a b := Subtype.ext hx
  rw [he]
  change fieldAut m sigma (torusAction m c (coordinateElement m a b)) =
    torusAction m (Units.map sigma.toMonoidHom c) (fieldAut m sigma (coordinateElement m a b))
  rw [torusAction_coordinateElement,fieldAut_coordinate,fieldAut_coordinate,
    torusAction_coordinateElement]
  change coordinateElement m (sigma ((c : Field m)⁻¹*a))
      (sigma (((c : Field m)*theta m (c : Field m))⁻¹*b)) =
    coordinateElement m ((sigma (c : Field m))⁻¹*sigma a)
      ((sigma (c : Field m)*theta m (sigma (c : Field m)))⁻¹*sigma b)
  simp only [map_mul,map_inv₀,theta_apply,map_pow]

theorem fieldAut_conjugate_torus (m : ℕ) (sigma : Field m ≃+* Field m)
    (c : (Field m)ˣ) :
    fieldAut m sigma*torusAutHom m c*(fieldAut m sigma)⁻¹ =
      torusAutHom m (Units.map sigma.toMonoidHom c) := by
  apply MulEquiv.ext
  intro x
  change fieldAut m sigma (torusAutHom m c ((fieldAut m sigma).symm x)) = _
  rw [fieldAut_torus_intertwines,(fieldAut m sigma).apply_symm_apply]

theorem fieldAut_mem_torus_normalizer (m : ℕ) (sigma : Field m ≃+* Field m) :
    fieldAut m sigma ∈ Subgroup.normalizer
      ((torusAutHom m).range : Set (MulAut (unipotentSubgroup m))) := by
  apply hom_mem_normalizer_of_conjugate_closed (fieldAutHom m) (torusAutHom m).range
    (fun tau R hR => ?_) sigma
  obtain ⟨c,rfl⟩ := hR
  exact ⟨Units.map tau.toMonoidHom c,(fieldAut_conjugate_torus m tau c).symm⟩

theorem eq_fieldAut_of_first (m : ℕ) (hm : 1 ≤ m)
    (f : MulAut (unipotentSubgroup m))
    (hf : f ∈ Subgroup.normalizer
      ((torusAutHom m).range : Set (MulAut (unipotentSubgroup m))))
    (sigma : Field m ≃+* Field m)
    (hfirst : ∀ x, firstParameter m (f x) = sigma (firstParameter m x)) :
    f = fieldAut m sigma := by
  let F : Subgroup.normalizer
      ((torusAutHom m).range : Set (MulAut (unipotentSubgroup m))) := ⟨f,hf⟩
  let S : Subgroup.normalizer
      ((torusAutHom m).range : Set (MulAut (unipotentSubgroup m))) :=
    ⟨fieldAut m sigma,fieldAut_mem_torus_normalizer m sigma⟩
  have he : normalizerFirstHom m hm F = normalizerFirstHom m hm S := by
    apply AddEquiv.ext
    intro a
    change firstLayerAddAut m hm f a = firstLayerAddAut m hm (fieldAut m sigma) a
    have hF := firstLayerAddAut_first m hm f (coordinateElement m a 0)
    have hS := firstLayerAddAut_first m hm (fieldAut m sigma) (coordinateElement m a 0)
    calc
      _ = firstParameter m (f (coordinateElement m a 0)) := hF
      _ = sigma a := hfirst (coordinateElement m a 0)
      _ = firstParameter m (fieldAut m sigma (coordinateElement m a 0)) :=
        (fieldAut_first m sigma (coordinateElement m a 0)).symm
      _ = _ := hS.symm
  exact congrArg Subtype.val (normalizerFirstHom_injective m hm he)

theorem coordinate_action_of_first (m : ℕ) (hm : 1 ≤ m)
    (f : MulAut (unipotentSubgroup m))
    (hf : f ∈ Subgroup.normalizer
      ((torusAutHom m).range : Set (MulAut (unipotentSubgroup m))))
    (sigma : Field m ≃+* Field m)
    (hfirst : ∀ x, firstParameter m (f x) = sigma (firstParameter m x)) (a b : Field m) :
    f (coordinateElement m a b) = coordinateElement m (sigma a) (sigma b) := by
  rw [eq_fieldAut_of_first m hm f hf sigma hfirst,fieldAut_coordinate]

end SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotentFieldActions
