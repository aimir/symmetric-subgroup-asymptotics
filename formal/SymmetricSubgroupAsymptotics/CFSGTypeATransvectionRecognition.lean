import SymmetricSubgroupAsymptotics.CFSGTypeATransvectionSylowCenters
import SymmetricSubgroupAsymptotics.CFSGSylowCenterConjugacy

/-! Intrinsic transvection recognition in the original finite SL group:
the concrete rank-one transvections, including the identity, are exactly
the union of the centres of defining-characteristic Sylow subgroups.
Consequently every abstract automorphism preserves this concrete family.
No assertion about a PSL representative is hidden in this SL statement. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeATransvectionRecognition
open Matrix Module LinearMap CFSGTypeAProjectivePointRoots CFSGTypeAElementaryMatrices
open CFSGSylowCenterRecognition CFSGTypeATransvectionHighestRoot
variable {F : Type*} [Field F] [Finite F] {n : ℕ}

def IsTransvection (A : Matrix.SpecialLinearGroup (Fin n) F) : Prop :=
  ∃f : Dual F (Fin n→F),∃v : Fin n→F,∃hfv : f v=0,A=transvectionSL hfv

omit [Finite F] in
private theorem elementary_as_transvection {i j : Fin n} (hij : i≠j) (a : F) :
    elementary hij a=transvectionSL
      (show (LinearMap.proj j : (Fin n→F)→ₗ[F]F) (a • Pi.single i 1)=0 by
        simp [Pi.single_apply,hij,eq_comm]) := by
  apply Matrix.SpecialLinearGroup.toLin'_injective
  apply LinearEquiv.ext
  intro x
  rw [elementary_apply,transvectionSL_apply]
  simp only [LinearMap.proj_apply,smul_smul,mul_comm]

theorem sylowCenterElements_isTransvection (p : ℕ) [Fact p.Prime] [CharP F p]
    (hn : 2≤n) {A : Matrix.SpecialLinearGroup (Fin n) F}
    (hA : A∈sylowCenterElements (G:=Matrix.SpecialLinearGroup (Fin n) F) p) :
    IsTransvection A := by
  let P := CFSGTypeAGoodSylow.actualUpperSylow F p n
  obtain ⟨g,z,hz,hg⟩ := exists_conjugate_fixed_sylow_center p P hA
  obtain ⟨a,ha⟩ := CFSGUpperUnitriangular.center_upperUnitriangular_eq_highestRoot hn z hz
  rw [ha,elementary_as_transvection,CFSGTypeAProjectivePointRoots.transvectionSL_conjugate] at hg
  exact ⟨_,_,_,hg.symm⟩

theorem isTransvection_mem_sylowCenterElements (p : ℕ) [Fact p.Prime] [CharP F p]
    (hn : 2≤n) {A : Matrix.SpecialLinearGroup (Fin n) F} (hA : IsTransvection A) :
    A∈sylowCenterElements (G:=Matrix.SpecialLinearGroup (Fin n) F) p := by
  obtain ⟨f,v,hfv,rfl⟩ := hA
  by_cases hf : f=0
  · subst f
    rw [transvectionSL_zero]
    exact one_mem_sylowCenterElements p
  by_cases hv : v=0
  · have he : transvectionSL hfv=1 := by
      apply Matrix.SpecialLinearGroup.toLin'_injective
      rw [map_one]
      apply LinearEquiv.ext
      intro x
      change (transvectionSL hfv).toLin' x=x
      simp only [transvectionSL_apply,hv,smul_zero,add_zero]
    rw [he]
    exact one_mem_sylowCenterElements p
  exact CFSGTypeATransvectionSylowCenters.transvection_mem_sylowCenterElements p hn f v hfv hf hv

theorem isTransvection_iff_sylowCenterElements (p : ℕ) [Fact p.Prime] [CharP F p]
    (hn : 2≤n) (A : Matrix.SpecialLinearGroup (Fin n) F) :
    IsTransvection A ↔ A∈sylowCenterElements (G:=Matrix.SpecialLinearGroup (Fin n) F) p :=
  ⟨isTransvection_mem_sylowCenterElements p hn,sylowCenterElements_isTransvection p hn⟩

theorem automorphism_isTransvection_iff (p : ℕ) [Fact p.Prime] [CharP F p]
    (hn : 2≤n) (f : MulAut (Matrix.SpecialLinearGroup (Fin n) F))
    (A : Matrix.SpecialLinearGroup (Fin n) F) : IsTransvection (f A) ↔ IsTransvection A := by
  rw [isTransvection_iff_sylowCenterElements p hn,isTransvection_iff_sylowCenterElements p hn]
  exact automorphism_mem_sylowCenterElements_iff p f A

end SymmetricSubgroupAsymptotics.CFSGTypeATransvectionRecognition
