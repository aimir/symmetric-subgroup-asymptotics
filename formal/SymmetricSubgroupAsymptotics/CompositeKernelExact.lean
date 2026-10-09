import SymmetricSubgroupAsymptotics.Non2LiftBound

/-!
# The exact kernel extension of a composite quotient

For surjective group maps `G → H → K`, the kernel of the composite maps
onto the kernel of the second map, and its kernel is literally the kernel
of the first map.  The constructions below retain the subgroup types.  In
particular they can be combined with the module charts on the two kernels
without replacing either layer by an abstract isomorphic group.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- Restrict the first map to the kernel of the composite. -/
def compositeKernelProjection (f : G →* H) (g : H →* K) :
    (g.comp f).ker →* g.ker where
  toFun x := ⟨f x.1, x.2⟩
  map_one' := by
    apply Subtype.ext
    exact map_one f
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul f x.1 y.1

@[simp] theorem compositeKernelProjection_apply
    (f : G →* H) (g : H →* K) (x : (g.comp f).ker) :
    (compositeKernelProjection f g x : H) = f x.1 :=
  rfl

/-- Surjectivity of the first map makes the restricted kernel map onto. -/
theorem compositeKernelProjection_surjective
    (f : G →* H) (g : H →* K)
    (hf : Function.Surjective f) :
    Function.Surjective (compositeKernelProjection f g) := by
  intro y
  obtain ⟨x, hx⟩ := hf y.1
  have hxker : x ∈ (g.comp f).ker := by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hx]
    exact y.2
  refine ⟨⟨x, hxker⟩, ?_⟩
  apply Subtype.ext
  exact hx

/-- The first kernel embeds in the composite kernel. -/
def compositeKernelInclusion (f : G →* H) (g : H →* K) :
    f.ker →* (g.comp f).ker where
  toFun x := ⟨x.1, by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
      MonoidHom.mem_ker.mp x.2, map_one]⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem compositeKernelInclusion_injective
    (f : G →* H) (g : H →* K) :
    Function.Injective (compositeKernelInclusion f g) := by
  intro x y hxy
  exact Subtype.ext (congrArg Subtype.val hxy)

/-- The two canonical maps form an exact sequence on the literal kernel
subgroups. -/
theorem compositeKernelInclusion_range_eq_projection_ker
    (f : G →* H) (g : H →* K) :
    (compositeKernelInclusion f g).range =
      (compositeKernelProjection f g).ker := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    exact MonoidHom.mem_ker.mp y.2
  · intro hx
    have hfx : f x.1 = 1 := by
      have := MonoidHom.mem_ker.mp hx
      exact congrArg Subtype.val this
    let y : f.ker := ⟨x.1, MonoidHom.mem_ker.mpr hfx⟩
    exact ⟨y, Subtype.ext rfl⟩

/-- The kernel of the restricted projection is canonically the first
kernel, with all inclusions given by the original group elements. -/
noncomputable def compositeKernelFiberEquiv
    (f : G →* H) (g : H →* K) :
    f.ker ≃* (compositeKernelProjection f g).ker := by
  let inclusion : f.ker →* (compositeKernelProjection f g).ker :=
    (compositeKernelInclusion f g).codRestrict
      (compositeKernelProjection f g).ker (by
        intro x
        rw [MonoidHom.mem_ker]
        apply Subtype.ext
        exact MonoidHom.mem_ker.mp x.2)
  apply MulEquiv.ofBijective inclusion
  constructor
  · intro x y hxy
    exact Subtype.ext (congrArg (fun z => ((z.1 : (g.comp f).ker) : G)) hxy)
  · intro x
    have hx : (compositeKernelInclusion f g).range x.1 := by
      rw [compositeKernelInclusion_range_eq_projection_ker]
      exact x.2
    obtain ⟨y, hy⟩ := hx
    refine ⟨y, ?_⟩
    apply Subtype.ext
    exact hy

end SymmetricSubgroupAsymptotics

end
