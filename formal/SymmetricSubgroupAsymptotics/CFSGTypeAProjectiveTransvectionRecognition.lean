import SymmetricSubgroupAsymptotics.CFSGTypeATransvectionHighestRoot
import SymmetricSubgroupAsymptotics.CFSGTypeAProjectiveUpperSylow
import SymmetricSubgroupAsymptotics.CFSGSylowCenterConjugacy

/-! Intrinsic recognition of original projective transvections. The
concrete image of rank-one determinant-one transvections is exactly the
union of centres of actual defining-characteristic Sylow subgroups.
Thus abstract PSL automorphisms preserve this family directly; no lift
of an arbitrary PSL automorphism to SL is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeAProjectiveTransvectionRecognition
open Matrix Module LinearMap CFSGTypeAProjectivePointRoots CFSGTypeAElementaryMatrices
open CFSGSylowCenterRecognition CFSGTypeATransvectionHighestRoot
variable {F : Type*} [Field F] [Finite F] {n : ℕ}

def IsProjectiveTransvection (x : Matrix.ProjectiveSpecialLinearGroup (Fin n) F) : Prop :=
  ∃f : Dual F (Fin n→F),∃v : Fin n→F,∃hfv : f v=0,x=projection (transvectionSL hfv)

omit [Finite F] in
private theorem elementary_rank_one {i j : Fin n} (hij : i≠j) (a : F) :
    ∃f : Dual F (Fin n→F),∃v : Fin n→F,∃hfv : f v=0,elementary hij a=transvectionSL hfv := by
  refine ⟨LinearMap.proj j,a • Pi.single i 1,by simp [Pi.single_apply,hij,eq_comm],?_⟩
  apply Matrix.SpecialLinearGroup.toLin'_injective
  apply LinearEquiv.ext
  intro x
  rw [elementary_apply,transvectionSL_apply]
  simp only [LinearMap.proj_apply,smul_smul,mul_comm]

theorem highestRoot_mem_sylowCenterElements (p : ℕ) [Fact p.Prime] [CharP F p]
    (hn : 2≤n) (a : F) :
    projection (elementary (show (⟨0,by omega⟩ : Fin n)≠⟨n-1,by omega⟩ by
      intro he;have hh := congrArg Fin.val he;dsimp only at hh;omega) a)∈
      sylowCenterElements (G:=Matrix.ProjectiveSpecialLinearGroup (Fin n) F) p := by
  obtain ⟨z,hz,hza⟩ := CFSGTypeAProjectiveUpperCenter.highestRoot_projectiveUpperSylow_center
    (F:=F) (n:=n) p hn a
  exact ⟨_,z,hz,hza⟩

theorem isProjectiveTransvection_mem_sylowCenterElements (p : ℕ) [Fact p.Prime] [CharP F p]
    (hn : 2≤n) {x : Matrix.ProjectiveSpecialLinearGroup (Fin n) F} (hx : IsProjectiveTransvection x) :
    x∈sylowCenterElements (G:=Matrix.ProjectiveSpecialLinearGroup (Fin n) F) p := by
  obtain ⟨f,v,hfv,rfl⟩ := hx
  by_cases hf : f=0
  · subst f
    rw [transvectionSL_zero,map_one]
    exact one_mem_sylowCenterElements p
  by_cases hv : v=0
  · have he : transvectionSL hfv=1 := by
      apply Matrix.SpecialLinearGroup.toLin'_injective
      rw [map_one]
      apply LinearEquiv.ext
      intro y
      change (transvectionSL hfv).toLin' y=y
      simp only [transvectionSL_apply,hv,smul_zero,add_zero]
    rw [he,map_one]
    exact one_mem_sylowCenterElements p
  obtain ⟨e,he⟩ := exists_linearConjugation_highestRoot hn f v hfv hf hv
  have hh : projectiveLinearConjugation e (projection (transvectionSL hfv))∈
      sylowCenterElements (G:=Matrix.ProjectiveSpecialLinearGroup (Fin n) F) p := by
    rw [projectiveLinearConjugation_apply,he]
    exact highestRoot_mem_sylowCenterElements p hn 1
  exact (automorphism_mem_sylowCenterElements_iff p (projectiveLinearConjugation e) _).mp hh

theorem sylowCenterElements_isProjectiveTransvection (p : ℕ) [Fact p.Prime] [CharP F p]
    (hn : 2≤n) {x : Matrix.ProjectiveSpecialLinearGroup (Fin n) F}
    (hx : x∈sylowCenterElements (G:=Matrix.ProjectiveSpecialLinearGroup (Fin n) F) p) :
    IsProjectiveTransvection x := by
  let P := CFSGTypeAProjectiveUpperCenter.projectiveUpperSylow (F:=F) (n:=n) p
  obtain ⟨g,z,hz,hg⟩ := exists_conjugate_fixed_sylow_center p P hx
  obtain ⟨a,ha⟩ := CFSGTypeAProjectiveUpperCenter.projectiveUpperSylow_center_highestRoot p hn z hz
  rw [ha] at hg
  obtain ⟨A,hA⟩ := QuotientGroup.mk'_surjective (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F)) g
  change projection A=g at hA
  rw [←hA] at hg
  obtain ⟨f,v,hfv,he⟩ := elementary_rank_one
    (show (⟨0,by omega⟩ : Fin n)≠⟨n-1,by omega⟩ by
      intro h;have hh := congrArg Fin.val h;dsimp only at hh;omega) a
  have hh : projection (A*transvectionSL hfv*A⁻¹)=x := by
    rw [map_mul,map_mul,map_inv,←he]
    exact hg
  rw [CFSGTypeAProjectivePointRoots.transvectionSL_conjugate] at hh
  exact ⟨_,_,_,hh.symm⟩

theorem isProjectiveTransvection_iff_sylowCenterElements (p : ℕ) [Fact p.Prime] [CharP F p]
    (hn : 2≤n) (x : Matrix.ProjectiveSpecialLinearGroup (Fin n) F) :
    IsProjectiveTransvection x ↔ x∈sylowCenterElements (G:=Matrix.ProjectiveSpecialLinearGroup (Fin n) F) p :=
  ⟨isProjectiveTransvection_mem_sylowCenterElements p hn,
    sylowCenterElements_isProjectiveTransvection p hn⟩

theorem automorphism_isProjectiveTransvection_iff (p : ℕ) [Fact p.Prime] [CharP F p]
    (hn : 2≤n) (f : MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) F))
    (x : Matrix.ProjectiveSpecialLinearGroup (Fin n) F) :
    IsProjectiveTransvection (f x) ↔ IsProjectiveTransvection x := by
  rw [isProjectiveTransvection_iff_sylowCenterElements p hn,
    isProjectiveTransvection_iff_sylowCenterElements p hn]
  exact automorphism_mem_sylowCenterElements_iff p f x

end SymmetricSubgroupAsymptotics.CFSGTypeAProjectiveTransvectionRecognition
