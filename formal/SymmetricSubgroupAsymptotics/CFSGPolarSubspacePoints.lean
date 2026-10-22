import SymmetricSubgroupAsymptotics.CFSGSingularPlaneTriangle
import SymmetricSubgroupAsymptotics.CFSGSingularPairSpan
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Literal singular points and subspaces, and their exact incidence.
These elementary linear facts require no polar-space classification. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints
open CFSGSingularPlaneTriangle
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

abbrev Points (B : LinearMap.BilinForm K V) :=
  {P : Submodule K V // Module.finrank K P=1 ∧ ZeroOn B P P}
abbrev Planes (B : LinearMap.BilinForm K V) :=
  {P : Submodule K V // Module.finrank K P=2 ∧ ZeroOn B P P}
abbrev Subspaces (B : LinearMap.BilinForm K V) :=
  {W : Submodule K V // ZeroOn B W W}

def ray (B : LinearMap.BilinForm K V) (v : V) (hv : v≠0) (hz : B v v=0) : Points B :=
  ⟨Submodule.span K {v},finrank_span_singleton hv,by
    intro x hx y hy
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨b,rfl⟩ := Submodule.mem_span_singleton.mp hy
    simp only [map_smul,LinearMap.smul_apply,hz,smul_zero]⟩

theorem point_span (B : LinearMap.BilinForm K V) (P : Points B)
    (v : V) (hvP : v∈P.val) (hv : v≠0) : Submodule.span K {v}=P.val :=
  Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hvP)
    (by rw [P.property.1,finrank_span_singleton hv])

theorem point_eq_of_common_nonzero (B : LinearMap.BilinForm K V) (P Q : Points B)
    (v : V) (hp : v∈P.val) (hq : v∈Q.val) (hv : v≠0) : P=Q :=
  Subtype.ext ((point_span B P v hp hv).symm.trans (point_span B Q v hq hv))

theorem point_nonzero (B : LinearMap.BilinForm K V) (P : Points B) :
    ∃v∈P.val,v≠0 := by
  apply Submodule.exists_mem_ne_zero_of_ne_bot
  exact Submodule.one_le_finrank_iff.mp (by rw [P.property.1])

def joinPlane (B : LinearMap.BilinForm K V) (W : Subspaces B) (P Q : Points B)
    (hP : P.val≤W.val) (hQ : Q.val≤W.val) (hne : P≠Q) : Planes B := by
  have hbot : (P.val⊓Q.val : Submodule K V)=⊥ := by
    by_contra hn
    have hlo : 1≤Module.finrank K (P.val⊓Q.val : Submodule K V) :=
      Submodule.one_le_finrank_iff.mpr hn
    have hp : P.val⊓Q.val=P.val := Submodule.eq_of_le_of_finrank_le inf_le_left
      (by rw [P.property.1];exact hlo)
    have hq : P.val⊓Q.val=Q.val := Submodule.eq_of_le_of_finrank_le inf_le_right
      (by rw [Q.property.1];exact hlo)
    exact hne (Subtype.ext (hp.symm.trans hq))
  have hd := Submodule.finrank_sup_add_finrank_inf_eq P.val Q.val
  rw [hbot,finrank_bot,P.property.1,Q.property.1,add_zero] at hd
  exact ⟨P.val⊔Q.val,hd,fun x hx y hy=>W.property x ((sup_le hP hQ) hx)
    y ((sup_le hP hQ) hy)⟩

theorem subspace_ext (B : LinearMap.BilinForm K V) {W Z : Subspaces B}
    (h : ∀P : Points B,P.val≤W.val ↔ P.val≤Z.val) : W=Z := by
  have hle : ∀ A C : Subspaces B,
      (∀P : Points B,P.val≤A.val → P.val≤C.val) → A.val≤C.val := by
    intro A C hac v hv
    by_cases hz : v=0
    · exact hz ▸ C.val.zero_mem
    let P := ray B v hz (A.property v hv v hv)
    have hp : P.val≤A.val := (Submodule.span_singleton_le_iff_mem _ _).mpr hv
    exact hac P hp (Submodule.subset_span (by simp))
  exact Subtype.ext (le_antisymm (hle W Z (fun P=>(h P).mp)) (hle Z W (fun P=>(h P).mpr)))

end SymmetricSubgroupAsymptotics.CFSGPolarSubspacePoints
