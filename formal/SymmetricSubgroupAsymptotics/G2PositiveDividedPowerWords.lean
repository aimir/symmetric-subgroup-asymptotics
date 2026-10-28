import Mathlib.Algebra.Lie.Derivation.Basic
import Mathlib.Tactic.Module

/-! Six original G2 positive DP words and their genuine source-side
raising actions. Only the two defining Serre relations enter; no native
representation, source faithfulness, dimension or finite action is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.G2PositiveDividedPowerWords
variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] (a b : L)

def c : L := ⁅a,b⁆
def d : L := (1/2 : ℚ) • ⁅a,c a b⁆
def e : L := (1/3 : ℚ) • ⁅a,d a b⁆
def f : L := ⁅b,e a b⁆

theorem a_c : ⁅a,c a b⁆ = (2:ℚ) • d a b := by
  rw [d]
  module

theorem a_d : ⁅a,d a b⁆ = (3:ℚ) • e a b := by
  rw [e]
  module

theorem b_a : ⁅b,a⁆ = -c a b := by
  exact (lie_skew b a).symm

theorem a_e (ha : ⁅a,⁅a,⁅a,⁅a,b⁆⁆⁆⁆ = 0) : ⁅a,e a b⁆ = 0 := by
  simp only [e,d,c,lie_smul,ha,smul_zero]

theorem b_c (hb : ⁅b,⁅b,a⁆⁆ = 0) : ⁅b,c a b⁆ = 0 := by
  have hc : c a b = -⁅b,a⁆ := (lie_skew a b).symm
  rw [hc,lie_neg,hb,neg_zero]

theorem b_d (hb : ⁅b,⁅b,a⁆⁆ = 0) : ⁅b,d a b⁆ = 0 := by
  rw [d,lie_smul,leibniz_lie,b_a a b,b_c a b hb,lie_zero,add_zero,
    neg_lie,lie_self,neg_zero,smul_zero]

theorem c_d (hb : ⁅b,⁅b,a⁆⁆ = 0) :
    ⁅c a b,d a b⁆ = (-3:ℚ) • f a b := by
  have h := leibniz_lie b a (d a b)
  rw [a_d a b,lie_smul,b_a a b,neg_lie,b_d a b hb,lie_zero,add_zero] at h
  change (3:ℚ) • f a b = -⁅c a b,d a b⁆ at h
  calc
    ⁅c a b,d a b⁆ = -(-⁅c a b,d a b⁆) := (neg_neg _).symm
    _ = -((3:ℚ) • f a b) := congrArg (fun v : L => -v) h.symm
    _ = (-3:ℚ) • f a b := by module

theorem a_f_eq_c_e (ha : ⁅a,⁅a,⁅a,⁅a,b⁆⁆⁆⁆ = 0) :
    ⁅a,f a b⁆ = ⁅c a b,e a b⁆ := by
  rw [f,leibniz_lie,a_e a b ha,lie_zero,add_zero]
  rfl

theorem c_e (ha : ⁅a,⁅a,⁅a,⁅a,b⁆⁆⁆⁆ = 0) (hb : ⁅b,⁅b,a⁆⁆ = 0) :
    ⁅c a b,e a b⁆ = 0 := by
  have h := congrArg (fun v : L => ⁅a,v⁆) (c_d a b hb)
  change ⁅a,⁅c a b,d a b⁆⁆ = ⁅a,(-3:ℚ) • f a b⁆ at h
  rw [leibniz_lie,a_c a b,a_d a b,smul_lie,lie_self,smul_zero,zero_add,
    lie_smul,lie_smul,a_f_eq_c_e a b ha] at h
  have hz : (6:ℚ) • ⁅c a b,e a b⁆ = 0 := by
    calc
      (6:ℚ) • ⁅c a b,e a b⁆ =
          (3:ℚ) • ⁅c a b,e a b⁆ - (-3:ℚ) • ⁅c a b,e a b⁆ := by module
      _ = 0 := sub_eq_zero.mpr h
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

theorem a_f (ha : ⁅a,⁅a,⁅a,⁅a,b⁆⁆⁆⁆ = 0) (hb : ⁅b,⁅b,a⁆⁆ = 0) :
    ⁅a,f a b⁆ = 0 := (a_f_eq_c_e a b ha).trans (c_e a b ha hb)

theorem b_f (hb : ⁅b,⁅b,a⁆⁆ = 0) : ⁅b,f a b⁆ = 0 := by
  have h := congrArg (fun v : L => ⁅b,v⁆) (c_d a b hb)
  change ⁅b,⁅c a b,d a b⁆⁆ = ⁅b,(-3:ℚ) • f a b⁆ at h
  rw [leibniz_lie,b_c a b hb,zero_lie,b_d a b hb,lie_zero,
    zero_add,lie_smul] at h
  exact (smul_eq_zero.mp h.symm).resolve_left (by norm_num)

/-- The two source root strings really are the divided-power words. -/
theorem d_eq_divided_square : d a b = (2:ℚ)⁻¹ • ((LieAlgebra.ad ℚ L a)^2) b := by
  simp only [d,c,pow_two,Module.End.mul_apply,LieAlgebra.ad_apply]
  norm_num

theorem e_eq_divided_cube : e a b = (6:ℚ)⁻¹ • ((LieAlgebra.ad ℚ L a)^3) b := by
  simp only [e,d,c,pow_succ',pow_zero,Module.End.mul_apply,Module.End.one_apply,
    LieAlgebra.ad_apply,lie_smul,smul_smul]
  norm_num

/-- Universal Cartan weights of the six selected source words. -/
theorem weights (h : L) (u v : ℚ) (hha : ⁅h,a⁆ = u • a) (hhb : ⁅h,b⁆ = v • b) :
    ⁅h,c a b⁆ = (u+v) • c a b ∧
    ⁅h,d a b⁆ = (2*u+v) • d a b ∧
    ⁅h,e a b⁆ = (3*u+v) • e a b ∧
    ⁅h,f a b⁆ = (3*u+2*v) • f a b := by
  have hc : ⁅h,c a b⁆ = (u+v) • c a b := by
    rw [c,leibniz_lie,hha,hhb,smul_lie,lie_smul]
    change u • ⁅a,b⁆ + v • ⁅a,b⁆ = (u+v) • ⁅a,b⁆
    module
  have hd : ⁅h,d a b⁆ = (2*u+v) • d a b := by
    rw [d,lie_smul,leibniz_lie,hha,hc,smul_lie,lie_smul]
    change _ = (2*u+v) • ((1/2:ℚ) • ⁅a,c a b⁆)
    module
  have he : ⁅h,e a b⁆ = (3*u+v) • e a b := by
    rw [e,lie_smul,leibniz_lie,hha,hd,smul_lie,lie_smul]
    change _ = (3*u+v) • ((1/3:ℚ) • ⁅a,d a b⁆)
    module
  have hf : ⁅h,f a b⁆ = (3*u+2*v) • f a b := by
    rw [f,leibniz_lie,hhb,he,smul_lie,lie_smul]
    change _ = (3*u+2*v) • ⁅b,e a b⁆
    module
  exact ⟨hc,hd,he,hf⟩

/-- All opposite-simple actions follow from the ORIGINAL mixed Serre and
Cartan rows. In particular no vanishing is inferred from a native image. -/
theorem lowerings (p q h0 h1 : L)
    (hpa : ⁅p,a⁆ = -h0) (hpb : ⁅p,b⁆ = 0)
    (hqa : ⁅q,a⁆ = 0) (hqb : ⁅q,b⁆ = -h1)
    (hh0a : ⁅h0,a⁆ = (2:ℚ) • a) (hh0b : ⁅h0,b⁆ = (-3:ℚ) • b)
    (hh1a : ⁅h1,a⁆ = (-1:ℚ) • a) (hh1b : ⁅h1,b⁆ = (2:ℚ) • b)
    (hb : ⁅b,⁅b,a⁆⁆ = 0) :
    ⁅p,c a b⁆ = (3:ℚ) • b ∧
    ⁅p,d a b⁆ = (2:ℚ) • c a b ∧
    ⁅p,e a b⁆ = d a b ∧ ⁅p,f a b⁆ = 0 ∧
    ⁅q,c a b⁆ = -a ∧ ⁅q,d a b⁆ = 0 ∧
    ⁅q,e a b⁆ = 0 ∧ ⁅q,f a b⁆ = e a b := by
  have h0c : ⁅h0,c a b⁆ = -c a b := by
    simpa only [show (2:ℚ)+(-3) = -1 by norm_num, neg_one_smul] using
      (weights a b h0 2 (-3) hh0a hh0b).1
  have h0d : ⁅h0,d a b⁆ = d a b := by
    simpa only [show 2*(2:ℚ)+(-3) = 1 by norm_num, one_smul] using
      (weights a b h0 2 (-3) hh0a hh0b).2.1
  have h1e : ⁅h1,e a b⁆ = -e a b := by
    simpa only [show 3*(-1:ℚ)+2 = -1 by norm_num, neg_one_smul] using
      (weights a b h1 (-1) 2 hh1a hh1b).2.2.1
  have hpc : ⁅p,c a b⁆ = (3:ℚ) • b := by
    rw [c,leibniz_lie,hpa,hpb,lie_zero,add_zero,neg_lie,hh0b]
    module
  have hpd : ⁅p,d a b⁆ = (2:ℚ) • c a b := by
    rw [d,lie_smul,leibniz_lie,hpa,neg_lie,h0c,hpc,lie_smul]
    change (1/2:ℚ) • (-(-c a b) + (3:ℚ) • c a b) = (2:ℚ) • c a b
    module
  have hpe : ⁅p,e a b⁆ = d a b := by
    rw [e,lie_smul,leibniz_lie,hpa,neg_lie,h0d,hpd,lie_smul,a_c]
    module
  have hpf : ⁅p,f a b⁆ = 0 := by
    rw [f,leibniz_lie,hpb,zero_lie,hpe,b_d a b hb,zero_add]
  have hqc : ⁅q,c a b⁆ = -a := by
    rw [c,leibniz_lie,hqa,zero_lie,hqb,zero_add,lie_neg,←lie_skew a h1,hh1a]
    module
  have hqd : ⁅q,d a b⁆ = 0 := by
    rw [d,lie_smul,leibniz_lie,hqa,zero_lie,hqc,lie_neg,lie_self,
      neg_zero,zero_add,smul_zero]
  have hqe : ⁅q,e a b⁆ = 0 := by
    rw [e,lie_smul,leibniz_lie,hqa,zero_lie,hqd,lie_zero,zero_add,smul_zero]
  have hqf : ⁅q,f a b⁆ = e a b := by
    rw [f,leibniz_lie,hqb,neg_lie,h1e,hqe,lie_zero,add_zero,neg_neg]
  exact ⟨hpc,hpd,hpe,hpf,hqc,hqd,hqe,hqf⟩

end SymmetricSubgroupAsymptotics.G2PositiveDividedPowerWords
