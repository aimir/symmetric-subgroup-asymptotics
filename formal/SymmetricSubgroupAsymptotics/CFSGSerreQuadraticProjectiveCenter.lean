import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrixActions
import SymmetricSubgroupAsymptotics.CFSGQuadraticRootScalarConjugacy
import SymmetricSubgroupAsymptotics.CFSGUnitConjugation
import Mathlib.Tactic.Group

/-! Centre-free quotient of an actual quadratic-root matrix group with
proved scalar centre. Scalar rigidity is cubic, and the proof commutes
with ALL original root units before invoking their actual closure. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I]
    (D : Data A I) (K : Type) [Field K]
    (U : Bool→Fin n→K→(Matrix I I K)ˣ)
    (hU : ∀neg i t,(U neg i t : Matrix I I K)=
      1+t • fieldRoot D K neg i+t^2 • fieldSecond D K neg i)

abbrev elementaryProjective := elementaryGroup K U ⧸ Subgroup.center (elementaryGroup K U)

variable (hscalar : ∀u : elementaryGroup K U,u∈Subgroup.center (elementaryGroup K U)↔
      ∃c : K,(u.val : Matrix I I K)=c • (1 : Matrix I I K))
    (j0 : I) (hdiag : ∀neg i,fieldRoot D K neg i j0 j0=0 ∧ fieldSecond D K neg i j0 j0=0)
include hU hscalar hdiag

theorem projective_central_lift_mem_center (u : elementaryGroup K U)
    (hu : (QuotientGroup.mk' (Subgroup.center (elementaryGroup K U))) u∈
      Subgroup.center (elementaryProjective K U)) : u∈Subgroup.center (elementaryGroup K U) := by
  let q := QuotientGroup.mk' (Subgroup.center (elementaryGroup K U))
  have hroot : ∀neg i t,u.val*U neg i t=U neg i t*u.val := by
    intro neg i t
    let v := elementaryRoot K U neg i t
    have hcomm : q v*q u=q u*q v := (Subgroup.mem_center_iff.mp hu) (q v)
    have hk : q (u*v*u⁻¹*v⁻¹)=1 := by
      simp only [map_mul,map_inv]
      rw [←hcomm]
      group
    have hz : u*v*u⁻¹*v⁻¹∈Subgroup.center (elementaryGroup K U) :=
      (QuotientGroup.eq_one_iff _).mp hk
    obtain ⟨c,hc⟩ := (hscalar (u*v*u⁻¹*v⁻¹)).mp hz
    have hm := congrArg (fun M : Matrix I I K=>M*(v.val : Matrix I I K)) hc
    change ((u.val : Matrix I I K)*(v.val : Matrix I I K)*
      (↑(u.val⁻¹):Matrix I I K)*(↑(v.val⁻¹):Matrix I I K))*(v.val : Matrix I I K)=
      (c • (1:Matrix I I K))*(v.val : Matrix I I K) at hm
    simp only [mul_assoc,Units.inv_mul,mul_one,smul_mul_assoc,one_mul] at hm
    have hconj : (u.val : Matrix I I K)*
        (1+t • fieldRoot D K neg i+t^2 • fieldSecond D K neg i)*
        (↑(u.val⁻¹):Matrix I I K)=
      c • (1+t • fieldRoot D K neg i+t^2 • fieldSecond D K neg i) := by
      have hv : (v.val : Matrix I I K)=(U neg i t : Matrix I I K) := rfl
      rw [hv] at hm
      simp only [hU] at hm
      simpa only [mul_assoc] using hm
    have hc1 : c=1 := CFSGQuadraticRootScalarConjugacy.scalar_conjugate_quadratic_root
      (fieldRoot D K neg i) (fieldSecond D K neg i)
      (fieldRoot_square D K neg i) (fieldRoot_mul_second D K neg i)
      (fieldSecond_mul_root D K neg i) (fieldSecond_square D K neg i)
      j0 (hdiag neg i).1 (hdiag neg i).2 u.val t c hconj
    simp only [hc1,one_smul] at hconj
    have hfix : (u.val : Matrix I I K)*(U neg i t : Matrix I I K)*
        (↑(u.val⁻¹):Matrix I I K)=(U neg i t : Matrix I I K) := by
      simpa only [hU] using hconj
    apply Units.ext
    exact (CFSGUnitConjugation.fix_iff_commute u.val _).mp hfix
  apply Subgroup.mem_center_iff.mpr
  have hle : elementaryGroup K U≤Subgroup.centralizer {u.val} := by
    apply (Subgroup.closure_le _).mpr
    rintro z ⟨neg,i,t,rfl⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro a ha
    have he : a=u.val := Set.mem_singleton_iff.mp ha
    subst a
    exact hroot neg i t
  intro v
  have hv := Subgroup.mem_centralizer_iff.mp (hle v.property) u.val (Set.mem_singleton _)
  exact Subtype.ext hv.symm

theorem elementaryProjective_center_eq_bot : Subgroup.center (elementaryProjective K U)=⊥ := by
  apply bot_unique
  intro z hz
  obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (elementaryGroup K U)) z
  change (QuotientGroup.mk' (Subgroup.center (elementaryGroup K U))) u=1
  exact (QuotientGroup.eq_one_iff u).mpr
    (projective_central_lift_mem_center D K U hU hscalar j0 hdiag u hz)

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
