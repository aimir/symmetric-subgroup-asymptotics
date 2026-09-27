import SymmetricSubgroupAsymptotics.RepresentationFixedExact
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Exact head filtration through original intertwining maps.

The dual sequence is exact because the original final map is onto.
Taking invariants then supplies the head inequality without assuming
that invariant forms extend from a submodule. The kernel and image
used below are the literal kernel and image of the original map.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.RepresentationHeadExact

variable {k G V W Z : Type} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    [AddCommGroup Z] [Module k Z]
    {ρ : Representation k G V} {σ : Representation k G W}
    {τ : Representation k G Z}

def dualMap (f : ρ.IntertwiningMap σ) : σ.dual.IntertwiningMap ρ.dual where
  toLinearMap := f.toLinearMap.dualMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro l
    apply LinearMap.ext
    intro v
    change l (σ g⁻¹ (f v))=l (f (ρ g⁻¹ v))
    exact congrArg l (Representation.IntertwiningMap.isIntertwining ρ σ f g⁻¹ v).symm

theorem dual_invariants_finrank_eq [FiniteDimensional k V] :
    Module.finrank k ρ.dual.invariants=
      Module.finrank k (ρ.IntertwiningMap (Representation.trivial k G k)) := by
  have he : ρ.dual=ρ.linHom (Representation.trivial k G k) := by
    ext g l v
    rfl
  rw [he]
  exact (Representation.invariantsEquivIntertwiningMap ρ
    (Representation.trivial k G k)).finrank_eq

/-- The actual source head is bounded by the actual submodule head and
actual quotient head. Surjectivity belongs to the original quotient map. -/
theorem head_finrank_le_of_range_eq_ker
    [FiniteDimensional k V] [FiniteDimensional k W] [FiniteDimensional k Z]
    (i : σ.IntertwiningMap ρ) (q : ρ.IntertwiningMap τ)
    (hq : Function.Surjective q) (hexact : i.toLinearMap.range=q.toLinearMap.ker) :
    Module.finrank k (ρ.IntertwiningMap (Representation.trivial k G k))≤
      Module.finrank k (σ.IntertwiningMap (Representation.trivial k G k))+
      Module.finrank k (τ.IntertwiningMap (Representation.trivial k G k)) := by
  have hi : Function.Injective (dualMap q) :=
    LinearMap.dualMap_injective_of_surjective hq
  have he : (dualMap q).toLinearMap.range=(dualMap i).toLinearMap.ker := by
    change q.toLinearMap.dualMap.range=i.toLinearMap.dualMap.ker
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker,
      LinearMap.ker_dualMap_eq_dualAnnihilator_range,hexact]
  have hd := RepresentationFixedExact.finrank_invariants_le_of_range_eq_ker
    (dualMap q) (dualMap i) hi he
  rw [dual_invariants_finrank_eq,dual_invariants_finrank_eq,
    dual_invariants_finrank_eq] at hd
  omega

def kernelInclusion (f : ρ.IntertwiningMap σ) : f.ker.toRepresentation.IntertwiningMap ρ where
  toLinearMap := f.ker.toSubmodule.subtype
  isIntertwining' _ := rfl

def rangeProjection (f : ρ.IntertwiningMap σ) : ρ.IntertwiningMap f.range.toRepresentation where
  toLinearMap := f.toLinearMap.rangeRestrict
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining ρ σ f g v

theorem rangeProjection_surjective (f : ρ.IntertwiningMap σ) :
    Function.Surjective (rangeProjection f) := by
  rintro ⟨w,⟨v,hv⟩⟩
  exact ⟨v,Subtype.ext hv⟩

theorem kernelInclusion_range (f : ρ.IntertwiningMap σ) :
    (kernelInclusion f).toLinearMap.range=(rangeProjection f).toLinearMap.ker := by
  ext v
  constructor
  · rintro ⟨a,rfl⟩
    exact Subtype.ext a.property
  · intro hv
    exact ⟨⟨v,congrArg Subtype.val hv⟩,rfl⟩

theorem head_finrank_le_kernel_add_range
    [FiniteDimensional k V] [FiniteDimensional k W]
    (f : ρ.IntertwiningMap σ) :
    Module.finrank k (ρ.IntertwiningMap (Representation.trivial k G k))≤
      Module.finrank k (f.ker.toRepresentation.IntertwiningMap (Representation.trivial k G k))+
      Module.finrank k (f.range.toRepresentation.IntertwiningMap (Representation.trivial k G k)) :=
  head_finrank_le_of_range_eq_ker (kernelInclusion f) (rangeProjection f)
    (rangeProjection_surjective f) (kernelInclusion_range f)

/-- Pullback along an actual representation equivalence transports its
entire head, with no ambient action change. -/
def headEquiv (e : ρ.Equiv σ) :
    (ρ.IntertwiningMap (Representation.trivial k G k)) ≃ₗ[k]
      (σ.IntertwiningMap (Representation.trivial k G k)) where
  toFun f := f.comp e.symm.toIntertwiningMap
  invFun f := f.comp e.toIntertwiningMap
  left_inv f := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    change f (e.symm (e v))=f v
    rw [e.symm_apply_apply]
  right_inv f := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    change f (e (e.symm v))=f v
    rw [e.apply_symm_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Exact two-coordinate filtration: the first term is the image in
coordinate one of the literal kernel of coordinate two. In particular
the result does not replace a correlated source by a product. -/
theorem head_finrank_le_two_coordinates
    [FiniteDimensional k V] [FiniteDimensional k W] [FiniteDimensional k Z]
    (f₁ : ρ.IntertwiningMap σ) (f₂ : ρ.IntertwiningMap τ)
    (hf : Function.Injective (fun v => (f₁ v,f₂ v))) :
    Module.finrank k (ρ.IntertwiningMap (Representation.trivial k G k))≤
      Module.finrank k ((f₁.comp (kernelInclusion f₂)).range.toRepresentation.IntertwiningMap
        (Representation.trivial k G k))+
      Module.finrank k (f₂.range.toRepresentation.IntertwiningMap (Representation.trivial k G k)) := by
  let f := f₁.comp (kernelInclusion f₂)
  have hi : Function.Injective f := by
    intro v w h
    apply Subtype.ext
    apply hf
    apply Prod.ext
    · exact h
    · exact v.property.trans w.property.symm
  have hi' : Function.Injective (rangeProjection f) := by
    intro v w h
    exact hi (congrArg Subtype.val h)
  let e := (rangeProjection f).ofBijective ⟨hi',rangeProjection_surjective f⟩
  have he := (headEquiv e).finrank_eq
  have hb := head_finrank_le_kernel_add_range f₂
  rw [he] at hb
  exact hb

end SymmetricSubgroupAsymptotics.RepresentationHeadExact
