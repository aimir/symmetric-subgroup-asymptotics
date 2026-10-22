import SymmetricSubgroupAsymptotics.CFSGQuadraticPolarMixedLinearRatio

/-! Maximal-space linearity supplies a concrete mixed-ray ratio. The
perpendicular hyperplane is nonzero by rank-nullity in dimension at
least three, and the required mixed space is constructed with its
original exact dimension. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspacePoints
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem restrictedKernel_ne_bot_of_three_le (q : QuadraticForm K V)
    (P : Subspaces q) (hd : 3≤Module.finrank K P.val) (y : V) :
    restrictedKernel q P y≠⊥ := by
  let f := restrictedPairing q P y
  have hr : Module.finrank K f.range≤1 := by
    simpa only [Module.finrank_self] using Submodule.finrank_le f.range
  have he := f.finrank_range_add_finrank_ker
  have hm := Submodule.finrank_map_subtype_eq P.val f.ker
  intro hz
  have hk : Module.finrank K (restrictedKernel q P y)=0 := by rw [hz,finrank_bot]
  change Module.finrank K (restrictedKernel q P y)=Module.finrank K f.ker at hm
  omega

theorem exists_mixed_ray_ratio (q : QuadraticForm K V)
    (f : Points q≃Points q) (P : Subspaces q) (hd : 3≤Module.finrank K P.val)
    (hlinear : ∀W : Subspaces q,Module.finrank K W.val=Module.finrank K P.val →
      Nonempty (SemilinearPiece q f W (RingEquiv.refl K)))
    (y : V) (hy : q y=0) (hyn : y∉P.val) (hf : restrictedPairing q P y≠0)
    (hfixP : ∀R : Points q,R.val≤P.val → f R=R)
    (hfixY : ∀R : Points q,R.val≤Submodule.span K {y} → f R=R) :
    ∃t : K,t≠0 ∧ ∀(x : V),x∈P.val → q.polarBilin y x=0 →
      ∀(hx0 : x+y≠0) (hz : q (x+y)=0),
        (f (ray q (x+y) hx0 hz)).val=Submodule.span K {x+t•y} := by
  let W := mixedSpace q P y hy
  have hdW : Module.finrank K W.val=Module.finrank K P.val := mixedSpace_finrank q P y hy hyn hf
  obtain ⟨t,ht,hall⟩ := mixedSpace_ray_ratio q f P y hy hyn
    (restrictedKernel_ne_bot_of_three_le q P hd y) (Classical.choice (hlinear W hdW)) hfixP hfixY
  exact ⟨t,ht,fun x hx hxy hx0 _=>hall x ((mem_restrictedKernel q P y x).mpr ⟨hx,hxy⟩) hx0⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspacePoints
