import SymmetricSubgroupAsymptotics.CFSGTypeAGeneralLinearCardBound
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! Actual projective point stabilizers in SL descend to proper subgroups
of the original PSL quotient, retaining their exact index. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGTypeAProjectivePointIndex
open Matrix MulAction
variable {F : Type*} [Field F] [Finite F]

abbrev Points (F : Type*) [Field F] (n : ℕ) := Projectivization F (Fin n→F)
abbrev SL (F : Type*) [Field F] (n : ℕ) := Matrix.SpecialLinearGroup (Fin n) F
abbrev PSL (F : Type*) [Field F] (n : ℕ) := Matrix.ProjectiveSpecialLinearGroup (Fin n) F

theorem points_card_mul_units (n : ℕ) :
    Nat.card (Points F n)*(Nat.card F-1)=Nat.card F^n-1 := by
  simpa only [Nat.card_fun,Nat.card_fin] using (Projectivization.card F (Fin n→F)).symm

theorem points_card_gt_one (n : ℕ) (hn : 2≤n) : 1<Nat.card (Points F n) := by
  have hq : 2≤Nat.card F := Finite.one_lt_card
  have hp : Nat.card F^2≤Nat.card F^n := Nat.pow_le_pow_right (by omega) hn
  have hstrict : Nat.card F<Nat.card F^2 := by rw [pow_two];nlinarith
  have hc := points_card_mul_units (F:=F) n
  by_contra hh
  have hsmall : Nat.card (Points F n)≤1 := by omega
  have hm := Nat.mul_le_mul_right (Nat.card F-1) hsmall
  omega

theorem center_le_point_stabilizer (n : ℕ) (hn : 1≤n) (x : Points F n) :
    Subgroup.center (SL F n)≤MulAction.stabilizer (SL F n) x := by
  intro A hA
  obtain ⟨r,hr,he⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have hr0 : r≠0 := by
    intro hz
    rw [Fintype.card_fin,hz,zero_pow (by omega : n≠0)] at hr
    exact zero_ne_one hr
  change A • x=x
  rw [←Projectivization.mk_rep x,Projectivization.smul_mk]
  apply (Projectivization.mk_eq_mk_iff F _ _ _ _).mpr
  refine ⟨Units.mk0 r hr0,?_⟩
  change r • x.rep=A.val *ᵥ x.rep
  rw [←he]
  ext i
  simp only [Matrix.scalar_apply,Matrix.mulVec_diagonal,Pi.smul_apply,smul_eq_mul]

theorem exists_proper_subgroup_of_point_index (n : ℕ) (hn : 2≤n) :
    ∃ H : Subgroup (PSL F n), H≠⊤ ∧ H.index=Nat.card (Points F n) := by
  letI : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  letI : IsPretransitive (SL F n) (Points F n) :=
    isPretransitive_of_is_two_pretransitive
  let x : Points F n := Classical.choice inferInstance
  let S : Subgroup (SL F n) := MulAction.stabilizer (SL F n) x
  let pi : SL F n→*PSL F n := QuotientGroup.mk' (Subgroup.center (SL F n))
  have hi : S.index=Nat.card (Points F n) := MulAction.index_stabilizer_of_transitive _ x
  have hS : S≠⊤ := by
    intro he
    rw [he,Subgroup.index_top] at hi
    have hc := points_card_gt_one (F:=F) n hn
    omega
  have hk : pi.ker≤S := by
    rw [QuotientGroup.ker_mk']
    exact center_le_point_stabilizer n (by omega) x
  have hp : Function.Surjective pi := QuotientGroup.mk'_surjective _
  refine ⟨S.map pi,?_,?_⟩
  · intro he
    have hc := Subgroup.comap_map_eq_self hk
    rw [he,Subgroup.comap_top] at hc
    exact hS hc.symm
  · exact (S.index_map_eq hp hk).trans hi

end SymmetricSubgroupAsymptotics.CFSGTypeAProjectivePointIndex
