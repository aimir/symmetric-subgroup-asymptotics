import SymmetricSubgroupAsymptotics.CFSGUpperUnitriangular
import Mathlib.Data.Matrix.Basis
import Lean.Elab.Tactic.Omega

/-! The centre of the original upper-unitriangular group is the actual
highest-root subgroup. Commutation with two sparse families of elementary
matrices recovers all entries, uniformly in the dimension and field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGUpperUnitriangular
open Matrix CFSGTypeAElementaryMatrices
variable {F : Type*} [Field F] {n : ℕ}

private theorem commutes_single_of_elementary (A : SL F n) {i j : Fin n} (hij : i≠j)
    (he : A*elementary hij (1 : F)=elementary hij 1*A) :
    A.val*Matrix.single i j 1=Matrix.single i j 1*A.val := by
  have hm := congrArg (fun g : SL F n => g.val) he
  change A.val*(1+Matrix.single i j 1)=(1+Matrix.single i j 1)*A.val at hm
  simp only [mul_add,add_mul,mul_one,one_mul] at hm
  exact add_left_cancel hm

private theorem row_zero_of_commutes_elementary (A : SL F n) {i j b : Fin n}
    (hij : i≠j) (hbj : b≠j)
    (he : A*elementary hij (1 : F)=elementary hij 1*A) : A.val j b=0 := by
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) F => M i b)
    (commutes_single_of_elementary A hij he)
  dsimp only at h
  simpa only [Matrix.mul_single_apply_of_ne (1 : F) i j i b hbj,
    Matrix.single_mul_apply_same,one_mul] using h.symm

private theorem column_zero_of_commutes_elementary (A : SL F n) {i j a : Fin n}
    (hij : i≠j) (hai : a≠i)
    (he : A*elementary hij (1 : F)=elementary hij 1*A) : A.val a i=0 := by
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) F => M a j)
    (commutes_single_of_elementary A hij he)
  dsimp only at h
  simpa only [Matrix.mul_single_apply_same,mul_one,
    Matrix.single_mul_apply_of_ne (1 : F) i j a j hai] using h

private theorem central_commutes_elementary (A : upperUnitriangular F n)
    (hA : A∈Subgroup.center (upperUnitriangular F n)) {i j : Fin n} (hij : i < j) :
    A.val*elementary (ne_of_lt hij) (1 : F)=elementary (ne_of_lt hij) 1*A.val := by
  let e : upperUnitriangular F n :=
    ⟨elementary (ne_of_lt hij) 1,elementary_mem_upperUnitriangular hij 1⟩
  exact (congrArg (fun g : upperUnitriangular F n => g.val)
    (Subgroup.mem_center_iff.mp hA e)).symm

/-- Every central unitriangular matrix has only its top-right entry free. -/
theorem center_upperUnitriangular_eq_highestRoot (hn : 2≤n)
    (A : upperUnitriangular F n) (hA : A∈Subgroup.center (upperUnitriangular F n)) :
    ∃a : F,A.val=elementary (show (⟨0,by omega⟩ : Fin n)≠⟨n-1,by omega⟩ by
      intro he;have hh := congrArg Fin.val he;dsimp only at hh;omega) a := by
  let first : Fin n := ⟨0,by omega⟩
  let last : Fin n := ⟨n-1,by omega⟩
  have hfl : first≠last := by intro he;have hh := congrArg Fin.val he;dsimp [first,last] at hh;omega
  refine ⟨A.val.val first last,?_⟩
  apply Subtype.ext
  change A.val.val=Matrix.transvection first last (A.val.val first last)
  ext i j
  by_cases hi : i=first
  · subst i
    by_cases hjl : j=last
    · subst j
      simp [Matrix.transvection,hfl]
    · by_cases hjf : j=first
      · subst j
        rw [A.property.2 first]
        simp [Matrix.transvection,hfl,eq_comm]
      · have hj : j < last := by
          have hjv := j.isLt
          have hjne : j.val≠n-1 := by intro h;exact hjl (Fin.ext h)
          change j.val < n-1
          omega
        have hz : A.val.val first j=0 := column_zero_of_commutes_elementary A.val
          (ne_of_lt hj) (Ne.symm hjf) (central_commutes_elementary A hA hj)
        rw [hz]
        simp [Matrix.transvection,Ne.symm hjf,hjl,eq_comm]
  · by_cases hij : i=j
    · subst j
      rw [A.property.2 i]
      simp [Matrix.transvection,hi,eq_comm]
    · have hfi : first < i := by
        have hiv : i.val≠0 := by intro h;exact hi (Fin.ext h)
        change 0 < i.val
        omega
      have hz : A.val.val i j=0 := row_zero_of_commutes_elementary A.val
        (ne_of_lt hfi) (Ne.symm hij) (central_commutes_elementary A hA hfi)
      rw [hz]
      simp [Matrix.transvection,hi,hij,eq_comm]

/-- Conversely the highest-root group is central in the same original U. -/
theorem highestRoot_mem_center_upperUnitriangular (hn : 2≤n) (a : F) :
    (⟨elementary (show (⟨0,by omega⟩ : Fin n)≠⟨n-1,by omega⟩ by
      intro he;have hh := congrArg Fin.val he;dsimp only at hh;omega) a,
      elementary_mem_upperUnitriangular (show (⟨0,by omega⟩ : Fin n)<⟨n-1,by omega⟩ by
        change 0 < n-1;omega) a⟩ : upperUnitriangular F n)∈
      Subgroup.center (upperUnitriangular F n) := by
  let first : Fin n := ⟨0,by omega⟩
  let last : Fin n := ⟨n-1,by omega⟩
  apply Subgroup.mem_center_iff.mpr
  intro B
  apply Subtype.ext
  apply Subtype.ext
  change B.val.val*(1+Matrix.single first last a)=(1+Matrix.single first last a)*B.val.val
  have hcol : ∀i : Fin n,B.val.val i first=if i=first then 1 else 0 := by
    intro i
    by_cases hi : i=first
    · subst i
      simp [B.property.2 first]
    · rw [if_neg hi]
      apply B.property.1
      have hiv : i.val≠0 := by intro h;exact hi (Fin.ext h)
      change 0 < i.val
      omega
  have hrow : ∀j : Fin n,B.val.val last j=if j=last then 1 else 0 := by
    intro j
    by_cases hj : j=last
    · subst j
      simp [B.property.2 last]
    · rw [if_neg hj]
      apply B.property.1
      have hjv := j.isLt
      have hjne : j.val≠n-1 := by intro h;exact hj (Fin.ext h)
      change j.val < n-1
      omega
  have hleft : B.val.val*Matrix.single first last a=Matrix.single first last a := by
    ext i j
    by_cases hj : j=last
    · subst j
      rw [Matrix.mul_single_apply_same,hcol]
      by_cases hi : i=first <;> simp [hi,eq_comm]
    · rw [Matrix.mul_single_apply_of_ne a first last i j hj]
      simp [hj,eq_comm]
  have hright : Matrix.single first last a*B.val.val=Matrix.single first last a := by
    ext i j
    by_cases hi : i=first
    · subst i
      rw [Matrix.single_mul_apply_same,hrow]
      by_cases hj : j=last <;> simp [hj,eq_comm]
    · rw [Matrix.single_mul_apply_of_ne a first last i j hi]
      simp [hi,eq_comm]
  simp only [mul_add,add_mul,mul_one,one_mul,hleft,hright]

end SymmetricSubgroupAsymptotics.CFSGUpperUnitriangular
