import SymmetricSubgroupAsymptotics.PrimitiveAffineCoarsePrimeMultiplicity

/-! One exact arithmetic table covers all composite primitive-affine
degrees below1024 except binary dimensions2 through5. Rows are prime and
dimension pairs, not action representatives or a group census. The two
selected pilots were checked before this bounded expansion. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineCoarseBoundedParameters
open PrimitiveAffineCoarsePrimeMultiplicity

def rows : Finset (ℕ × ℕ × ℕ) :=
  {(2,6,96), (2,7,112), (2,8,128), (2,9,144),
   (3,2,51), (3,3,77), (3,4,102), (3,5,127), (3,6,153),
   (5,2,75), (5,3,112), (5,4,149), (7,2,90), (7,3,135),
   (11,2,111), (13,2,119), (17,2,131), (19,2,136),
   (23,2,145), (29,2,156), (31,2,159)}

theorem row_arithmetic : ∀ r ∈ rows,
    (r.1 ^ r.2.1) ^ 16 ≤ 2 ^ r.2.2 ∧
      (linearBudget r.1 r.2.1 - 1) ^ 2 * r.2.2 < 16 * (r.1 ^ r.2.1) ^ 2 := by
  decide +kernel

theorem bounded_coverage : ∀ (p : Fin 32) (d : Fin 10),
    p.val.Prime → 2 ≤ d.val → p.val ^ d.val < 1024 →
    (p.val = 2 → 6 ≤ d.val) →
      ∃ r ∈ rows, r.1 = p.val ∧ r.2.1 = d.val := by
  decide +kernel

theorem genRank_le_ceiling
    {G X : Type} [Group G] [Finite G] [Finite X] [Nontrivial X]
    [MulAction G X] [FaithfulSMul G X]
    (P : PrimitiveAffineProfile G X) (hprimitive : MulAction.IsPreprimitive G X)
    (C : P.ElementaryChart hprimitive)
    (hd : 2 ≤ C.d) (hsmall : P.p ^ C.d < 1024)
    (hbinary : P.p = 2 → 6 ≤ C.d) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  have hd10 : C.d < 10 := by
    by_contra h
    have h10 : 10 ≤ C.d := by omega
    have hpow := (Nat.pow_le_pow_left P.p_prime.two_le 10).trans
      (Nat.pow_le_pow_right P.p_prime.pos h10)
    norm_num at hpow
    omega
  have hp32 : P.p < 32 := by
    have hpow := Nat.pow_le_pow_right P.p_prime.pos hd
    by_contra h
    have hp : 32 ≤ P.p := by omega
    have h2 : P.p ^ 2 < 1024 := hpow.trans_lt hsmall
    nlinarith
  obtain ⟨r, hr, hp, hd⟩ := bounded_coverage ⟨P.p, hp32⟩ ⟨C.d, hd10⟩
    P.p_prime hd hsmall hbinary
  have h := row_arithmetic r hr
  rw [hp, hd] at h
  exact genRank_le_ceiling_of_arithmetic P hprimitive C 16 r.2.2 (by decide) h.1 h.2

end SymmetricSubgroupAsymptotics.PrimitiveAffineCoarseBoundedParameters
