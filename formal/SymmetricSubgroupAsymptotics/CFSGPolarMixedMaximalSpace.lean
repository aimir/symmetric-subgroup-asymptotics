import SymmetricSubgroupAsymptotics.CFSGPolarPointFunctionals

/-! Replacing one hyperplane of a singular space by an actual singular
vector constructs a singular space of the SAME dimension. Its dimension
and perpendicular kernel are proved, rather than supplied by a polar
space recognition premise. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints
open CFSGSingularPlaneTriangle
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

def restrictedKernel (B : LinearMap.BilinForm K V) (P : Subspaces B) (y : V) : Submodule K V :=
  (restrictedPairing B P y).ker.map P.val.subtype

theorem mem_restrictedKernel (B : LinearMap.BilinForm K V) (P : Subspaces B) (y x : V) :
    x∈restrictedKernel B P y ↔ x∈P.val ∧ B y x=0 := by
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x.property,hx⟩
  · rintro ⟨hx,hxy⟩
    exact ⟨⟨x,hx⟩,hxy,rfl⟩

theorem restrictedKernel_le (B : LinearMap.BilinForm K V) (P : Subspaces B) (y : V) :
    restrictedKernel B P y≤P.val := fun x hx=>(mem_restrictedKernel B P y x).mp hx |>.1

def mixedSpace (B : LinearMap.BilinForm K V) (hs : ∀x y,B x y=B y x)
    (P : Subspaces B) (y : V) (hy : B y y=0) : Subspaces B :=
  ⟨restrictedKernel B P y⊔Submodule.span K {y},by
    apply CFSGSingularPairSpan.zeroOn_sup B hs
    · exact fun x hx z hz=>P.property x (restrictedKernel_le B P y hx) z (restrictedKernel_le B P y hz)
    · intro u hu v hv
      obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hu
      obtain ⟨b,rfl⟩ := Submodule.mem_span_singleton.mp hv
      simp only [map_smul,LinearMap.smul_apply,hy,smul_zero]
    · intro x hx v hv
      obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hv
      rw [map_smul,hs x y,(mem_restrictedKernel B P y x).mp hx |>.2,smul_zero]⟩

theorem mixedSpace_finrank (B : LinearMap.BilinForm K V) (hs : ∀x y,B x y=B y x)
    (P : Subspaces B) (y : V) (hy : B y y=0) (hyn : y∉P.val)
    (hf : restrictedPairing B P y≠0) :
    Module.finrank K (mixedSpace B hs P y hy).val=Module.finrank K P.val := by
  let f := restrictedPairing B P y
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
  have hK : Module.finrank K (restrictedKernel B P y)=Module.finrank K f.ker :=
    Submodule.finrank_map_subtype_eq P.val f.ker
  have hy0 : y≠0 := by intro h;exact hyn (h ▸ P.val.zero_mem)
  have hd : Disjoint (restrictedKernel B P y) (Submodule.span K {y}) :=
    Submodule.disjoint_span_singleton_of_notMem (fun h=>hyn (restrictedKernel_le B P y h))
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (restrictedKernel B P y) (Submodule.span K {y})
  rw [hd.eq_bot,finrank_bot,finrank_span_singleton hy0,hK,add_zero] at hdim
  change Module.finrank K (restrictedKernel B P y⊔Submodule.span K {y} : Submodule K V)=_
  omega

end SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints
