import SymmetricSubgroupAsymptotics.AffineClassResidualReduction
import SymmetricSubgroupAsymptotics.PrimeDegreeAffineAllSubgroupsClassBound
import SymmetricSubgroupAsymptotics.AffinePrimePowerSubgroupClassBound
import Mathlib.Tactic.NormNum.Prime

/-! The exact original affine-profile GM residual consists of five
nonlinear degrees. The eliminated prime/square/cube families are proved
uniformly, without an elementary or primitive action premise. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AffineClassFiveDegreeResidual

def ResidualDegree (n : ℕ) : Prop := n=4 ∨ n=8 ∨ n=9 ∨ n=16 ∨ n=32

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (P : PrimitiveAffineProfile G X)

include P in
theorem subgroup_class_cube_or_residual (x : X) (hn : 4 ≤ Nat.card X) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) ∨ ResidualDegree (Nat.card X) := by
  rcases AffineClassResidualReduction.subgroup_class_cube_or_residual P x hn H with hGM | hres
  · exact Or.inl hGM
  letI : Fact P.p.Prime := ⟨P.p_prime⟩
  have hdvd : P.p ∣ Nat.card X := by
    have h := P.V_pgroup.card_eq_or_dvd
    rw [P.card_eq x] at h
    exact h.resolve_left (by omega)
  rcases hres with h4 | h5 | h7 | h8 | h9 | h16 | h25 | h27 | h32 | h49
  · exact Or.inr (Or.inl h4)
  · exact Or.inl (PrimeDegreeAffineAllSubgroupsClassBound.subgroup_class_cube_le_garonziMaroti
      P x (by rw [h5]; decide) hn H)
  · exact Or.inl (PrimeDegreeAffineAllSubgroupsClassBound.subgroup_class_cube_le_garonziMaroti
      P x (by rw [h7]; decide) hn H)
  · exact Or.inr (Or.inr (Or.inl h8))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h9)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h16))))
  · have hbase : P.p=5 := Nat.prime_eq_prime_of_dvd_pow (m := 2) P.p_prime
      (by decide : Nat.Prime 5) (by simpa only [h25,show (5:ℕ)^2=25 by norm_num] using hdvd)
    exact Or.inl (AffinePrimePowerSubgroupClassBound.subgroup_square_degree_cube_le P x
      (by rw [hbase]) (by simpa only [hbase,show (5:ℕ)^2=25 by norm_num] using h25) H)
  · have hbase : P.p=3 := Nat.prime_eq_prime_of_dvd_pow (m := 3) P.p_prime
      (by decide : Nat.Prime 3) (by simpa only [h27,show (3:ℕ)^3=27 by norm_num] using hdvd)
    exact Or.inl (AffinePrimePowerSubgroupClassBound.subgroup_cube_degree_cube_le P x
      (by rw [hbase]) (by simpa only [hbase,show (3:ℕ)^3=27 by norm_num] using h27) H)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h32))))
  · have hbase : P.p=7 := Nat.prime_eq_prime_of_dvd_pow (m := 2) P.p_prime
      (by decide : Nat.Prime 7) (by simpa only [h49,show (7:ℕ)^2=49 by norm_num] using hdvd)
    exact Or.inl (AffinePrimePowerSubgroupClassBound.subgroup_square_degree_cube_le P x
      (by rw [hbase]; decide) (by simpa only [hbase,show (7:ℕ)^2=49 by norm_num] using h49) H)

end SymmetricSubgroupAsymptotics.AffineClassFiveDegreeResidual
