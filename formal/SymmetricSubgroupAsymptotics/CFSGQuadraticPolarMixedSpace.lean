import SymmetricSubgroupAsymptotics.CFSGQuadraticPolarPointFunctionals

/-! The actual perpendicular-hyperplane replacement construction for
Q-singular spaces, uniformly in characteristic two. Q=0 is proved on
the whole new space and is not weakened to polar self-orthogonality. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspacePoints
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

def restrictedKernel (q : QuadraticForm K V) (P : Subspaces q) (y : V) : Submodule K V :=
  (restrictedPairing q P y).ker.map P.val.subtype

omit [FiniteDimensional K V] in
theorem mem_restrictedKernel (q : QuadraticForm K V) (P : Subspaces q) (y x : V) :
    x∈restrictedKernel q P y ↔ x∈P.val ∧ q.polarBilin y x=0 := by
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x.property,hx⟩
  · rintro ⟨hx,hxy⟩
    exact ⟨⟨x,hx⟩,hxy,rfl⟩

theorem restrictedKernel_le (q : QuadraticForm K V) (P : Subspaces q) (y : V) :
    restrictedKernel q P y≤P.val := fun x hx=>(mem_restrictedKernel q P y x).mp hx |>.1

def mixedSpace (q : QuadraticForm K V) (P : Subspaces q) (y : V) (hy : q y=0) : Subspaces q :=
  ⟨restrictedKernel q P y⊔Submodule.span K {y},by
    intro v hv
    obtain ⟨x,hx,z,hz,rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hz
    have hqx : q x=0 := P.property x (restrictedKernel_le q P y hx)
    have hyx : q.polarBilin y x=0 := ((mem_restrictedKernel q P y x).mp hx).2
    have hxy : q.polarBilin x y=0 := (QuadraticMap.polar_comm q x y).trans hyx
    rw [QuadraticMap.map_add q x (a•y)]
    change q x+q (a•y)+q.polarBilin x (a•y)=0
    rw [hqx,q.map_smul,hy,smul_zero,map_smul,hxy,smul_zero,add_zero,add_zero]⟩

theorem mixedSpace_finrank (q : QuadraticForm K V)
    (P : Subspaces q) (y : V) (hy : q y=0) (hyn : y∉P.val)
    (hf : restrictedPairing q P y≠0) :
    Module.finrank K (mixedSpace q P y hy).val=Module.finrank K P.val := by
  let f := restrictedPairing q P y
  have hr0 : f.range≠⊥ := by
    intro hz
    apply hf
    ext x
    have hx : f x∈f.range := ⟨x,rfl⟩
    rw [hz] at hx
    exact hx
  have hr1 : Module.finrank K f.range=1 := by
    have hlo := Submodule.one_le_finrank_iff.mpr hr0
    have hhi := Submodule.finrank_le f.range
    rw [Module.finrank_self] at hhi
    omega
  have hk := f.finrank_range_add_finrank_ker
  rw [hr1] at hk
  have hK : Module.finrank K (restrictedKernel q P y)=Module.finrank K f.ker :=
    Submodule.finrank_map_subtype_eq P.val f.ker
  have hy0 : y≠0 := by intro h;exact hyn (h ▸ P.val.zero_mem)
  have hd : Disjoint (restrictedKernel q P y) (Submodule.span K {y}) :=
    Submodule.disjoint_span_singleton_of_notMem (fun h=>hyn (restrictedKernel_le q P y h))
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (restrictedKernel q P y) (Submodule.span K {y})
  rw [hd.eq_bot,finrank_bot,finrank_span_singleton hy0,hK,add_zero] at hdim
  change Module.finrank K (restrictedKernel q P y⊔Submodule.span K {y} : Submodule K V)=_
  omega

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticSubspacePoints
