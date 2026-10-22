import SymmetricSubgroupAsymptotics.CFSGPolarMixedRatioExistence
import SymmetricSubgroupAsymptotics.CFSGIndependentPairRayRatio
import SymmetricSubgroupAsymptotics.CFSGTwoFunctionalKernelVector

/-! Linear pieces on the actual maximal singular spaces have ONE
common mixed scalar across an opposed pair. Rank-three common kernels
connect every pair of negative directions. The proof uses reciprocal
ratios from the very same point image, not independently chosen
worst-case estimates on the two halves. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem opposed_common_ratio (B : LinearMap.BilinForm K V) (hs : ∀x y,B x y=B y x)
    (f : Points B≃Points B) (P Z : Subspaces B) (hd : 3≤Module.finrank K P.val)
    (hdZ : Module.finrank K Z.val=Module.finrank K P.val) (hdis : Disjoint P.val Z.val)
    (hpairP : ∀y∈Z.val,y≠0 → restrictedPairing B P y≠0)
    (hpairZ : ∀x∈P.val,x≠0 → restrictedPairing B Z x≠0)
    (hlinear : ∀W : Subspaces B,Module.finrank K W.val=Module.finrank K P.val →
      Nonempty (SemilinearPiece B f W (RingEquiv.refl K)))
    (hfixP : ∀R : Points B,R.val≤P.val → f R=R)
    (hfixZ : ∀R : Points B,R.val≤Z.val → f R=R) :
    ∃t : K,t≠0 ∧ ∀(x y : V),x∈P.val → x≠0 → y∈Z.val → y≠0 → B y x=0 →
      ∀(hx0 : x+y≠0) (hz : B (x+y) (x+y)=0),
        (f (ray B (x+y) hx0 hz)).val=Submodule.span K {x+t•y} := by
  have hnotP (y : V) (hy : y∈Z.val) (hy0 : y≠0) : y∉P.val := by
    intro hp
    have hi : y∈(P.val⊓Z.val : Submodule K V) := ⟨hp,hy⟩
    rw [hdis.eq_bot] at hi
    exact hy0 hi
  have hnotZ (x : V) (hx : x∈P.val) (hx0 : x≠0) : x∉Z.val := by
    intro hz
    have hi : x∈(P.val⊓Z.val : Submodule K V) := ⟨hx,hz⟩
    rw [hdis.eq_bot] at hi
    exact hx0 hi
  let X := {x : P.val // x≠0}
  let Y := {y : Z.val // y≠0}
  have hX (x : X) : x.val.val≠0 := fun h=>x.property (Subtype.ext h)
  have hY (y : Y) : y.val.val≠0 := fun h=>y.property (Subtype.ext h)
  have hright (y : Y) := exists_mixed_ray_ratio B hs f P hd hlinear y.val.val
    (Z.property _ y.val.property _ y.val.property) (hnotP _ y.val.property (hY y))
    (hpairP _ y.val.property (hY y)) hfixP
    (fun R hR=>hfixZ R (hR.trans ((Submodule.span_singleton_le_iff_mem _ _).mpr y.val.property)))
  have hleft (x : X) := exists_mixed_ray_ratio B hs f Z (by omega)
    (fun W hW=>hlinear W (hW.trans hdZ)) x.val.val
    (P.property _ x.val.property _ x.val.property) (hnotZ _ x.val.property (hX x))
    (hpairZ _ x.val.property (hX x)) hfixZ
    (fun R hR=>hfixP R (hR.trans ((Submodule.span_singleton_le_iff_mem _ _).mpr x.val.property)))
  choose t ht htr using hright
  choose u hu hur using hleft
  have hproduct (x : X) (y : Y) (hxy : B y.val.val x.val.val=0) : t y*u x=1 := by
    have hsum0 : x.val.val+y.val.val≠0 := by
      intro hz
      have hyneg : y.val.val= -x.val.val := by rw [add_eq_zero_iff_eq_neg.mp hz,neg_neg]
      exact hnotP _ y.val.property (hY y) (hyneg ▸ P.val.neg_mem x.val.property)
    have hsum0' : y.val.val+x.val.val≠0 := by simpa only [add_comm] using hsum0
    have hsum : B (x.val.val+y.val.val) (x.val.val+y.val.val)=0 := by
      simp only [map_add,LinearMap.add_apply,P.property _ x.val.property _ x.val.property,
        Z.property _ y.val.property _ y.val.property,hxy,hs x.val.val y.val.val,add_zero]
    have hsum' : B (y.val.val+x.val.val) (y.val.val+x.val.val)=0 := by
      simpa only [add_comm] using hsum
    have hrep : ray B (y.val.val+x.val.val) hsum0' hsum'=
        ray B (x.val.val+y.val.val) hsum0 hsum := by
      apply Subtype.ext
      change Submodule.span K {y.val.val+x.val.val}=Submodule.span K {x.val.val+y.val.val}
      rw [add_comm]
    have hR := htr y x.val.val x.val.property hxy hsum0 hsum
    have hL := hur x y.val.val y.val.property ((hs x.val.val y.val.val).trans hxy) hsum0' hsum'
    have he : Submodule.span K {x.val.val+t y•y.val.val}=
        Submodule.span K {y.val.val+u x•x.val.val} :=
      hR.symm.trans ((congrArg (fun R : Points B=>(f R).val) hrep.symm).trans hL)
    have hli : LinearIndependent K ![x.val.val,y.val.val] :=
      (LinearIndependent.pair_iff' (hX x)).mpr (fun c he=>
        hnotP _ y.val.property (hY y) (he ▸ P.val.smul_mem c x.val.property))
    exact CFSGIndependentPairRayRatio.product_eq_one _ _ hli _ _ he
  have hconstant (a b : Y) : t a=t b := by
    obtain ⟨v,hv,hv0,hva,hvb⟩ := CFSGTwoFunctionalKernelVector.exists_nonzero_common_kernel
      P.val hd (B a.val.val) (B b.val.val)
    let x : X := ⟨⟨v,hv⟩,fun h=>hv0 (congrArg Subtype.val h)⟩
    exact mul_right_cancel₀ (hu x) ((hproduct x a hva).trans (hproduct x b hvb).symm)
  obtain ⟨y,hy,hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p:=Z.val)
    (Submodule.one_le_finrank_iff.mp (by omega : 1≤Module.finrank K Z.val))
  let y0 : Y := ⟨⟨y,hy⟩,fun h=>hy0 (congrArg Subtype.val h)⟩
  refine ⟨t y0,ht y0,?_⟩
  intro x y hx hx0 hy hy0 hxy hsum0 hsum
  let y' : Y := ⟨⟨y,hy⟩,fun h=>hy0 (congrArg Subtype.val h)⟩
  have he := htr y' x hx hxy hsum0 hsum
  rw [hconstant y' y0] at he
  exact he

end SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints
