import SymmetricSubgroupAsymptotics.CFSGSerreSquareZeroMatrixActions
import SymmetricSubgroupAsymptotics.CFSGMatrixUnipotentScalar
import SymmetricSubgroupAsymptotics.CFSGUnitConjugation
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.Group

/-! Shared centre-free projective quotient of a literal square-zero root
matrix group with an actually proved scalar centre. No order formula or
characteristic restriction is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreSquareZeroMatrix
variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I]
    (D : Data A I) (K : Type) [Field K]
    (U : Bool→Fin n→K→(Matrix I I K)ˣ)
    (hU : ∀neg i t,(U neg i t : Matrix I I K)=1+t • fieldRoot D K neg i)
    (hUi : ∀neg i t,(↑((U neg i t)⁻¹) : Matrix I I K)=1-t • fieldRoot D K neg i)

abbrev elementaryProjective := elementaryGroup K U ⧸ Subgroup.center (elementaryGroup K U)

variable (hscalar : ∀u : elementaryGroup K U,u∈Subgroup.center (elementaryGroup K U)↔
      ∃c : K,(u.val : Matrix I I K)=c • (1 : Matrix I I K))
    (j0 : I) (hdiag : ∀neg i,fieldRoot D K neg i j0 j0=0)
include hU hUi hscalar hdiag

theorem projective_central_lift_mem_center (u : elementaryGroup K U)
    (hu : (QuotientGroup.mk' (Subgroup.center (elementaryGroup K U))) u∈
      Subgroup.center (elementaryProjective K U)) : u∈Subgroup.center (elementaryGroup K U) := by
  let q := QuotientGroup.mk' (Subgroup.center (elementaryGroup K U))
  apply (hscalar u).mpr
  have hroot : ∀neg i,(u.val : Matrix I I K)*fieldRoot D K neg i=
      fieldRoot D K neg i*(u.val : Matrix I I K) := by
    intro neg i
    let v := elementaryRoot K U neg i (1:K)
    have hcomm : q v*q u=q u*q v := (Subgroup.mem_center_iff.mp hu) (q v)
    have hk : q (u*v*u⁻¹*v⁻¹)=1 := by
      simp only [map_mul,map_inv]
      rw [←hcomm]
      group
    have hz : u*v*u⁻¹*v⁻¹∈Subgroup.center (elementaryGroup K U) :=
      (QuotientGroup.eq_one_iff _).mp hk
    obtain ⟨c,hc⟩ := (hscalar (u*v*u⁻¹*v⁻¹)).mp hz
    have hm := congrArg (fun M : Matrix I I K => M*(v.val : Matrix I I K)) hc
    change ((u.val : Matrix I I K)*(v.val : Matrix I I K)*
      (↑(u.val⁻¹):Matrix I I K)*(↑(v.val⁻¹):Matrix I I K))*(v.val : Matrix I I K)=
      (c • (1:Matrix I I K))*(v.val : Matrix I I K) at hm
    simp only [mul_assoc,Units.inv_mul,mul_one,smul_mul_assoc,one_mul] at hm
    have hconj : (u.val : Matrix I I K)*(1+(1:K) • fieldRoot D K neg i)*
        (↑(u.val⁻¹):Matrix I I K)=c • (1+(1:K) • fieldRoot D K neg i) := by
      simpa only [v,elementaryRoot,hU,mul_assoc] using hm
    have hc1 : c=1 := CFSGMatrixUnipotentScalar.scalar_conjugate_transvection
      (fieldRoot D K neg i) (fieldRoot_sq_zero D K neg i) j0 (hdiag neg i) u.val 1 c hconj
    simp only [hc1,one_smul] at hconj
    have hh := (CFSGUnitConjugation.fix_iff_commute u.val _).mp hconj
    simp only [mul_add,add_mul,mul_one,one_mul] at hh
    exact add_left_cancel hh
  have hcentral : u∈Subgroup.center (elementaryGroup K U) := by
    apply Subgroup.mem_center_iff.mpr
    have hle : elementaryGroup K U≤Subgroup.centralizer {u.val} := by
      apply (Subgroup.closure_le _).mpr
      rintro z ⟨neg,i,t,rfl⟩
      apply Subgroup.mem_centralizer_iff.mpr
      intro a ha
      have he : a=u.val := Set.mem_singleton_iff.mp ha
      subst a
      apply Units.ext
      change (u.val : Matrix I I K)*(U neg i t : Matrix I I K)=
        (U neg i t : Matrix I I K)*(u.val : Matrix I I K)
      rw [hU]
      simp only [mul_add,add_mul,mul_one,one_mul,mul_smul_comm,smul_mul_assoc,hroot]
    intro v
    have hv := Subgroup.mem_centralizer_iff.mp (hle v.property) u.val (Set.mem_singleton _)
    exact Subtype.ext hv.symm
  exact (hscalar u).mp hcentral

theorem elementaryProjective_center_eq_bot :
    Subgroup.center (elementaryProjective K U)=⊥ := by
  apply bot_unique
  intro z hz
  obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (elementaryGroup K U)) z
  change (QuotientGroup.mk' (Subgroup.center (elementaryGroup K U))) u=1
  exact (QuotientGroup.eq_one_iff u).mpr
    (projective_central_lift_mem_center D K U hU hUi hscalar j0 hdiag u hz)

end SymmetricSubgroupAsymptotics.CFSGSerreSquareZeroMatrix
