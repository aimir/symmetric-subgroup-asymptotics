import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Tactic.Group

/-! Exact arm-product periods from ONLY involutions and their local
Coxeter-chain relations. The proofs are displayed group-word identities,
not finite-group recognition, enumeration, or supplied order assertions. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.InvolutionChainShortPeriods
variable {G : Type*} [Group G]

private theorem braid (a b : G) (ha : a^2 = 1) (hb : b^2 = 1)
    (hab : (a*b)^3 = 1) : a*b*a = b*a*b := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using ha)
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hb)
  have hh : (a*b*a)*(b*a*b) = 1 := by
    simpa only [pow_succ,pow_zero,mul_one,one_mul,mul_assoc] using hab
  have he := eq_inv_of_mul_eq_one_left hh
  simpa only [mul_inv_rev,hai,hbi,mul_assoc] using he

/-- The whole product on an actual three-node arm has period four. -/
theorem three_chain_period_four (a b c : G)
    (ha : a^2 = 1) (hb : b^2 = 1) (hc : c^2 = 1)
    (hab : (a*b)^3 = 1) (hbc : (b*c)^3 = 1) (hac : Commute a c) :
    (a*b*c)^4 = 1 := by
  have hab' := braid a b ha hb hab
  have hbc' := braid b c hb hc hbc
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hb)
  have hmid : (a*c)^2 = 1 := by rw [hac.mul_pow,ha,hc,mul_one]
  have hsquare : (a*b*c)^2 = b*a*c*b := by
    calc
      (a*b*c)^2 = a*b*(c*a)*b*c := by simp only [pow_two]; group
      _ = a*b*(a*c)*b*c := by rw [hac.symm.eq]
      _ = (a*b*a)*c*b*c := by group
      _ = (b*a*b)*c*b*c := by rw [hab']
      _ = b*a*(b*c*b)*c := by group
      _ = b*a*(c*b*c)*c := by rw [hbc']
      _ = b*a*c*b*(c*c) := by group
      _ = b*a*c*b := by rw [← pow_two,hc,mul_one]
  have hsquare' : (a*b*c)^2 = b*(a*c)*b⁻¹ := by
    rw [hbi]
    simpa only [mul_assoc] using hsquare
  calc
    (a*b*c)^4 = ((a*b*c)^2)^2 := by rw [← pow_mul]
    _ = (b*(a*c)*b⁻¹)^2 := by rw [hsquare']
    _ = b*(a*c)^2*b⁻¹ := by simp only [pow_two]; group
    _ = 1 := by rw [hmid,mul_one,mul_inv_cancel]

/-- The whole product on an actual four-node arm has period five. -/
theorem four_chain_period_five (a b c d : G)
    (ha : a^2 = 1) (hb : b^2 = 1) (hc : c^2 = 1) (hd : d^2 = 1)
    (hab : (a*b)^3 = 1) (hbc : (b*c)^3 = 1) (hcd : (c*d)^3 = 1)
    (hac : Commute a c) (had : Commute a d) (hbd : Commute b d) :
    (a*b*c*d)^5 = 1 := by
  have hab' := braid a b ha hb hab
  have hbc' := braid b c hb hc hbc
  have hcd' := braid c d hc hd hcd
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using ha)
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hb)
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hc)
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hd)
  have hcda : c*d*a = a*c*d := by
    rw [mul_assoc,had.symm.eq,← mul_assoc,hac.symm.eq]
  have hdca : d*c*a = a*d*c := by
    rw [mul_assoc,hac.symm.eq,← mul_assoc,had.symm.eq]
  have hsquare : (a*b*c*d)^2 = b*a*c*b*d*c := by
    calc
      (a*b*c*d)^2 = a*b*(c*d*a)*b*c*d := by simp only [pow_two]; group
      _ = a*b*(a*c*d)*b*c*d := by rw [hcda]
      _ = (a*b*a)*c*(d*b)*c*d := by group
      _ = (b*a*b)*c*(b*d)*c*d := by rw [hab',hbd.symm.eq]
      _ = b*a*(b*c*b)*(d*c*d) := by group
      _ = b*a*(c*b*c)*(c*d*c) := by rw [hbc',← hcd']
      _ = b*a*c*b*(c*c)*d*c := by group
      _ = b*a*c*b*d*c := by rw [← pow_two,hc]; group
  have hcube : (a*b*c*d)^3 = c*b*a*d*c*b := by
    calc
      (a*b*c*d)^3 = ((a*b*c*d)^2)*(a*b*c*d) := by rw [pow_succ]
      _ = b*a*c*b*(d*c*a)*b*c*d := by rw [hsquare]; group
      _ = b*a*c*b*(a*d*c)*b*c*d := by rw [hdca]
      _ = b*(a*c)*(b*a)*d*c*b*c*d := by group
      _ = b*(c*a)*(b*a)*d*c*b*c*d := by rw [hac.eq]
      _ = (b*c)*(a*b*a)*d*c*b*c*d := by group
      _ = (b*c)*(b*a*b)*d*c*b*c*d := by rw [hab']
      _ = (b*c*b)*a*b*d*c*b*c*d := by group
      _ = (c*b*c)*a*b*d*c*b*c*d := by rw [hbc']
      _ = c*b*(c*a)*(b*d)*c*b*c*d := by group
      _ = c*b*(a*c)*(d*b)*c*b*c*d := by rw [hac.symm.eq,hbd.eq]
      _ = c*b*a*c*d*(b*c*b)*c*d := by group
      _ = c*b*a*c*d*(c*b*c)*c*d := by rw [hbc']
      _ = c*b*a*c*d*c*b*(c*c)*d := by group
      _ = c*b*a*c*d*c*b*d := by rw [← pow_two,hc]; group
      _ = c*b*a*(c*d*c)*b*d := by group
      _ = c*b*a*(d*c*d)*b*d := by rw [hcd']
      _ = c*b*a*d*c*(d*b)*d := by group
      _ = c*b*a*d*c*(b*d)*d := by rw [hbd.symm.eq]
      _ = c*b*a*d*c*b*(d*d) := by group
      _ = c*b*a*d*c*b := by rw [← pow_two,hd,mul_one]
  have hinverse : ((a*b*c*d)^2)⁻¹ = c*b*a*d*c*b := by
    rw [hsquare]
    calc
      (b*a*c*b*d*c)⁻¹ = c*d*b*c*a*b := by
        simp only [mul_inv_rev,hai,hbi,hci,hdi,mul_assoc]
      _ = c*(d*b)*c*a*b := by group
      _ = c*(b*d)*c*a*b := by rw [hbd.symm.eq]
      _ = c*b*(d*c*a)*b := by group
      _ = c*b*(a*d*c)*b := by rw [hdca]
      _ = c*b*a*d*c*b := by group
  calc
    (a*b*c*d)^5 = (a*b*c*d)^2*(a*b*c*d)^3 := by rw [← pow_add]
    _ = (a*b*c*d)^2*((a*b*c*d)^2)⁻¹ := by rw [hcube,hinverse]
    _ = 1 := mul_inv_cancel _

end SymmetricSubgroupAsymptotics.InvolutionChainShortPeriods
