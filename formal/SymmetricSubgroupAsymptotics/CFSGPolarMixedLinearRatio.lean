import SymmetricSubgroupAsymptotics.CFSGPolarMixedMaximalSpace
import SymmetricSubgroupAsymptotics.CFSGPolarFixedLinearRestriction

/-! A linear representative on the actual mixed singular space gives
ONE nonzero ratio for all its mixed rays. The ratio is independent of
the vector in the perpendicular hyperplane; neither a coordinatewise
choice nor a ray-incidence hypothesis substitutes for this conclusion. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem mixedSpace_ray_ratio (B : LinearMap.BilinForm K V) (hs : ∀x y,B x y=B y x)
    (f : Points B≃Points B) (P : Subspaces B) (y : V) (hy : B y y=0)
    (hyn : y∉P.val) (hK : restrictedKernel B P y≠⊥)
    (F : SemilinearPiece B f (mixedSpace B hs P y hy) (RingEquiv.refl K))
    (hfixP : ∀R : Points B,R.val≤P.val → f R=R)
    (hfixY : ∀R : Points B,R.val≤Submodule.span K {y} → f R=R) :
    ∃t : K,t≠0 ∧ ∀(x : V) (hx : x∈restrictedKernel B P y)
      (hx0 : x+y≠0),
      (f (ray B (x+y) hx0
        ((mixedSpace B hs P y hy).property (x+y)
          (Submodule.add_mem_sup hx (Submodule.mem_span_singleton_self y)) (x+y)
          (Submodule.add_mem_sup hx (Submodule.mem_span_singleton_self y))))).val=
        Submodule.span K {x+t•y} := by
  let W := mixedSpace B hs P y hy
  have hKW : restrictedKernel B P y≤W.val := le_sup_left
  have hYW : Submodule.span K {y}≤W.val := le_sup_right
  obtain ⟨a,ha,haF⟩ := fixed_restriction_scalar_nonzero B f W F
    (restrictedKernel B P y) hKW hK
    (fun R hR=>hfixP R (hR.trans (restrictedKernel_le B P y)))
  have hy0 : y≠0 := by intro h;exact hyn (h ▸ P.val.zero_mem)
  have hY : (Submodule.span K {y} : Submodule K V)≠⊥ := by
    intro h
    have hm : y∈(⊥ : Submodule K V) := h ▸ Submodule.mem_span_singleton_self y
    exact hy0 hm
  obtain ⟨b,hb,hbF⟩ := fixed_restriction_scalar_nonzero B f W F
    (Submodule.span K {y}) hYW hY hfixY
  refine ⟨b/a,div_ne_zero hb ha,?_⟩
  intro x hx hx0
  have hxW : x∈W.val := hKW hx
  have hyW : y∈W.val := hYW (Submodule.mem_span_singleton_self y)
  have hxy : x+y∈W.val := W.val.add_mem hxW hyW
  have hxy0 : (⟨x+y,hxy⟩ : W.val)≠0 := fun h=>hx0 (congrArg Subtype.val h)
  have hsum : F.map ⟨x+y,hxy⟩=a•x+b•y := by
    have he := F.map.map_add (⟨x,hxW⟩ : W.val) (⟨y,hyW⟩ : W.val)
    change F.map ⟨x+y,hxy⟩=F.map ⟨x,hxW⟩+F.map ⟨y,hyW⟩ at he
    rw [haF ⟨x,hx⟩,hbF ⟨y,Submodule.mem_span_singleton_self y⟩] at he
    exact he
  have hscale : a•x+b•y=a•(x+(b/a)•y) := by
    rw [smul_add,smul_smul]
    congr 1
    congr 1
    field_simp
  have hp := F.point ⟨x+y,hxy⟩ hxy0
  change (f (ray B (x+y) hx0 (W.property (x+y) hxy (x+y) hxy))).val=_
  rw [←hp,hsum,hscale]
  exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr ha) _

end SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints
