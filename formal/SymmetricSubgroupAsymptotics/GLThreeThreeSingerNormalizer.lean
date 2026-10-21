import SymmetricSubgroupAsymptotics.StandardThreeDimensionalLinearGroups
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Group

/-! A selected Singer13 normalizer bound. Only a13th-power and twelve
trace pairs are finite receipts. Intertwiners are determined by their
first column, so the normalizer embeds in three times26 actual vectors.
There is no enumeration of GL3 subgroups or a multiplication table. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.GLThreeThreeSingerNormalizer
open StandardThreeDimensionalLinearGroups
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
local instance : Fact (Nat.Prime 13) := ⟨by decide⟩

abbrev M := Matrix (Fin 3) (Fin 3) (ZMod 3)
abbrev V := Fin 3 → ZMod 3

def A : M := !![0,0,1;1,0,1;0,1,0]

theorem A_pow : A^13=1 := by decide +kernel

def singer : GeneralThree 3 where
  val := A
  inv := A^12
  val_inv := by rw [←pow_succ',A_pow]
  inv_val := by rw [←pow_succ,A_pow]

@[simp] theorem singer_val : singer.val=A := rfl

theorem singer_order : orderOf singer=13 := by
  apply orderOf_eq_prime
  · apply Units.ext
    exact A_pow
  · intro h
    have he := congrArg (fun x : GeneralThree 3 => x 0 0) h
    norm_num [singer,A] at he

private theorem trace_power_receipt : ∀ k : Fin 13,
    Matrix.trace (A^k.val)=Matrix.trace A →
    Matrix.trace (A^(2*k.val))=Matrix.trace (A^2) →
    k.val=1 ∨ k.val=3 ∨ k.val=9 := by decide +kernel

private theorem mul_A_column_zero (B : M) (i : Fin 3) : (B*A) i 0=B i 1 := by
  simp [Matrix.mul_apply,Fin.sum_univ_three,A]

private theorem mul_A_column_one (B : M) (i : Fin 3) : (B*A) i 1=B i 2 := by
  simp [Matrix.mul_apply,Fin.sum_univ_three,A]

/-- This is an actual intertwiner statement for the fixed cyclic basis. -/
theorem intertwiner_ext {B C D : M} (hB : B*A=D*B) (hC : C*A=D*C)
    (hzero : ∀ i,B i 0=C i 0) : B=C := by
  have hone (i : Fin 3) : B i 1=C i 1 := calc
    B i 1=(B*A) i 0 := (mul_A_column_zero B i).symm
    _=(D*B) i 0 := congrFun (congrFun hB i) 0
    _=(D*C) i 0 := by simp only [Matrix.mul_apply,hzero]
    _=(C*A) i 0 := (congrFun (congrFun hC i) 0).symm
    _=C i 1 := mul_A_column_zero C i
  have htwo (i : Fin 3) : B i 2=C i 2 := calc
    B i 2=(B*A) i 1 := (mul_A_column_one B i).symm
    _=(D*B) i 1 := congrFun (congrFun hB i) 1
    _=(D*C) i 1 := by simp only [Matrix.mul_apply,hone]
    _=(C*A) i 1 := (congrFun (congrFun hC i) 1).symm
    _=C i 2 := mul_A_column_one C i
  ext i j
  fin_cases j
  · exact hzero i
  · exact hone i
  · exact htwo i

private theorem first_column_ne_zero (g : GeneralThree 3) :
    (fun i : Fin 3 => g i 0)≠0 := by
  intro h
  have he := congrArg (fun B : M => B 0 0) g.inv_val
  have hz (i : Fin 3) : g i 0=0 := congrFun h i
  simp [Matrix.mul_apply,hz] at he

private theorem trace_conj (g a : GeneralThree 3) :
    Matrix.trace (g*a*g⁻¹).val=Matrix.trace a.val := by
  exact Matrix.trace_units_conj g a.val

private theorem normalizer_power (g : Subgroup.normalizer
    (Subgroup.zpowers singer : Set (GeneralThree 3))) :
    ∃ k : Fin 13,(k.val=1 ∨ k.val=3 ∨ k.val=9) ∧
      g.val*singer*g.val⁻¹=singer^k.val := by
  have hmem : g.val*singer*g.val⁻¹∈Subgroup.zpowers singer :=
    (Subgroup.mem_normalizer_iff.mp g.property singer).mp (Subgroup.mem_zpowers singer)
  have hfin := (isOfFinOrder_of_finite singer).mem_zpowers_iff_mem_range_orderOf.mp hmem
  obtain ⟨k,hk,hpow⟩ := Finset.mem_image.mp hfin
  have hk13 : k<13 := by simpa only [singer_order] using Finset.mem_range.mp hk
  have he : g.val*singer*g.val⁻¹=singer^k := hpow.symm
  have he2 : g.val*singer^2*g.val⁻¹=singer^(2*k) := by
    calc
      _=(g.val*singer*g.val⁻¹)^2 := by
        simp only [pow_two,mul_assoc,inv_mul_cancel_left]
      _=(singer^k)^2 := congrArg (fun x : GeneralThree 3 => x^2) he
      _=_ := by rw [←pow_mul,Nat.mul_comm]
  refine ⟨⟨k,hk13⟩,trace_power_receipt ⟨k,hk13⟩ ?_ ?_,he⟩
  · have ht := trace_conj g.val singer
    rw [he] at ht
    exact ht
  · have ht := trace_conj g.val (singer^2)
    rw [he2] at ht
    exact ht

private theorem exponent_card :
    Nat.card {k : Fin 13 // k.val=1 ∨ k.val=3 ∨ k.val=9}=3 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem nonzero_vector_card : Nat.card {v : V // v≠0}=26 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

/-- The actual Singer normalizer costs at most78 elements. -/
theorem normalizer_card_le :
    Nat.card (Subgroup.normalizer (Subgroup.zpowers singer : Set (GeneralThree 3)))≤78 := by
  let E := {k : Fin 13 // k.val=1 ∨ k.val=3 ∨ k.val=9}
  let nz := {v : V // v≠0}
  let N := Subgroup.normalizer (Subgroup.zpowers singer : Set (GeneralThree 3))
  let k (g : N) : Fin 13 := Classical.choose (normalizer_power g)
  have hk (g : N) : (k g).val=1 ∨ (k g).val=3 ∨ (k g).val=9 :=
    (Classical.choose_spec (normalizer_power g)).1
  have he (g : N) : g.val*singer*g.val⁻¹=singer^(k g).val :=
    (Classical.choose_spec (normalizer_power g)).2
  let encode : N → E × nz := fun g =>
    (⟨k g,hk g⟩,⟨fun i => g.val i 0,first_column_ne_zero g.val⟩)
  have hi : Function.Injective encode := by
    intro g h hgh
    have hke : k g=k h := congrArg (fun z : E × nz => z.1.val) hgh
    have hcol : ∀ i,g.val i 0=h.val i 0 := fun i =>
      congrArg (fun z : E × nz => z.2.val i) hgh
    apply Subtype.ext
    apply Units.ext
    apply intertwiner_ext (D := (singer^(k g).val).val) _ _ hcol
    · have hx := (mul_inv_eq_iff_eq_mul).mp (he g)
      exact congrArg Units.val hx
    · have hx := (mul_inv_eq_iff_eq_mul).mp (he h)
      rw [hke]
      exact congrArg Units.val hx
  have hcard := Nat.card_le_card_of_injective encode hi
  simpa only [Nat.card_prod,E,nz,exponent_card,nonzero_vector_card] using hcard

/-- All actual order13 subgroups have the same normalizer order by Sylow,
so the selected Singer calculation supplies the generic bound. -/
theorem order_thirteen_normalizer_card_le (P : Subgroup (GeneralThree 3))
    (hP : Nat.card P=13) :
    Nat.card (Subgroup.normalizer (P : Set (GeneralThree 3)))≤78 := by
  have hpow : 13^(Nat.card (GeneralThree 3)).factorization 13=13 := by
    rw [card_GL_three]
    decide +kernel
  let SP : Sylow 13 (GeneralThree 3) := Sylow.ofCard P (hP.trans hpow.symm)
  let S0 : Sylow 13 (GeneralThree 3) := Sylow.ofCard (Subgroup.zpowers singer) (by
    rw [Nat.card_zpowers,singer_order]
    exact hpow.symm)
  have hidx : (Subgroup.normalizer (P : Set (GeneralThree 3))).index=
      (Subgroup.normalizer (Subgroup.zpowers singer : Set (GeneralThree 3))).index :=
    SP.card_eq_index_normalizer.symm.trans S0.card_eq_index_normalizer
  have hm := (Subgroup.normalizer (P : Set (GeneralThree 3))).card_mul_index
  have h0 := (Subgroup.normalizer
    (Subgroup.zpowers singer : Set (GeneralThree 3))).card_mul_index
  rw [hidx] at hm
  have he : Nat.card (Subgroup.normalizer (P : Set (GeneralThree 3)))=
      Nat.card (Subgroup.normalizer (Subgroup.zpowers singer : Set (GeneralThree 3))) :=
    mul_right_cancel₀ (Subgroup.index_ne_zero_of_finite (H := Subgroup.normalizer
      (Subgroup.zpowers singer : Set (GeneralThree 3)))) (hm.trans h0.symm)
  rw [he]
  exact normalizer_card_le

end SymmetricSubgroupAsymptotics.GLThreeThreeSingerNormalizer
