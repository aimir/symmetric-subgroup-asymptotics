import SymmetricSubgroupAsymptotics.CFSGPolarMixedLinearRatio

/-! Maximal-space linearity supplies a concrete mixed-ray ratio. The
perpendicular hyperplane is nonzero by rank-nullity in dimension at
least three, and the required mixed space is constructed with its
original exact dimension. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem restrictedKernel_ne_bot_of_three_le (B : LinearMap.BilinForm K V)
    (P : Subspaces B) (hd : 3≤Module.finrank K P.val) (y : V) :
    restrictedKernel B P y≠⊥ := by
  let f := restrictedPairing B P y
  have hr : Module.finrank K f.range≤1 := by
    simpa only [Module.finrank_self] using Submodule.finrank_le f.range
  have he := f.finrank_range_add_finrank_ker
  have hm := Submodule.finrank_map_subtype_eq P.val f.ker
  intro hz
  have hk : Module.finrank K (restrictedKernel B P y)=0 := by rw [hz,finrank_bot]
  change Module.finrank K (restrictedKernel B P y)=Module.finrank K f.ker at hm
  omega

theorem exists_mixed_ray_ratio (B : LinearMap.BilinForm K V) (hs : ∀x y,B x y=B y x)
    (f : Points B≃Points B) (P : Subspaces B) (hd : 3≤Module.finrank K P.val)
    (hlinear : ∀W : Subspaces B,Module.finrank K W.val=Module.finrank K P.val →
      Nonempty (SemilinearPiece B f W (RingEquiv.refl K)))
    (y : V) (hy : B y y=0) (hyn : y∉P.val) (hf : restrictedPairing B P y≠0)
    (hfixP : ∀R : Points B,R.val≤P.val → f R=R)
    (hfixY : ∀R : Points B,R.val≤Submodule.span K {y} → f R=R) :
    ∃t : K,t≠0 ∧ ∀(x : V),x∈P.val → B y x=0 →
      ∀(hx0 : x+y≠0) (hz : B (x+y) (x+y)=0),
        (f (ray B (x+y) hx0 hz)).val=Submodule.span K {x+t•y} := by
  let W := mixedSpace B hs P y hy
  have hdW : Module.finrank K W.val=Module.finrank K P.val := mixedSpace_finrank B hs P y hy hyn hf
  obtain ⟨t,ht,hall⟩ := mixedSpace_ray_ratio B hs f P y hy hyn
    (restrictedKernel_ne_bot_of_three_le B P hd y) (Classical.choice (hlinear W hdW)) hfixP hfixY
  exact ⟨t,ht,fun x hx hxy hx0 _=>hall x ((mem_restrictedKernel B P y x).mpr ⟨hx,hxy⟩) hx0⟩

end SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints
