import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryProjectiveCover
import SymmetricSubgroupAsymptotics.CFSGTwistedA2FixedRadicalKernel
import SymmetricSubgroupAsymptotics.CFSGInvolutionOrder

/-! Actual signed reversal gives parity in EVERY original twisted-A tag.
In rank>=3, its square is scalar and the proved full-centre cover kills
exactly the scalar kernel; an off-diagonal entry proves nontriviality.
Rank2 uses its proved actual inverse identity and projective flag escape.
No named-unitary recognition, known order, finite/simple/hn premise or
new central-kernel assumption occurs. The rank2 small guard is retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAReversalEvenOrder
open CFSGTwistedANaturalMatrices CFSGTwistedAUnitaryCoordinates
open CFSGTwistedAUpperUnipotent

private theorem even_card_of_nontrivial_square {G : Type*} [Group G] (x : G)
    (hx : x^2=1) (hne : x≠1) : Even (Nat.card G) := by
  by_contra he
  exact hne (CFSGReduction.eq_one_of_square_eq_one_of_odd_card
    (Nat.not_even_iff_odd.mp he) x hx)

theorem signedReversal_square_scalar (K : Type*) [Field K] (r : ℕ) :
    (signedReversalUnit K r : Mat K r) * (signedReversalUnit K r : Mat K r) =
      ((-1 : K)^r) • (1 : Mat K r) := by
  have he : ((-1 : K)^r)*((-1 : K)^r)=1 := by
    rw [←mul_pow]
    simp only [neg_one_mul,neg_neg,one_pow]
  have h := congrArg (fun M : Mat K r => ((-1 : K)^r) • M)
    (signedReversalUnit_orthogonal K r)
  dsimp only at h
  rw [signedReversalUnit_transpose,smul_mul_assoc,smul_smul,he,one_smul] at h
  exact h

theorem signedReversal_not_scalar (K : Type*) [Field K] (r : ℕ) (hr : 1≤r) :
    ¬∃ c : K, (signedReversalUnit K r : Mat K r)=c • 1 := by
  rintro ⟨c,hc⟩
  have hlast : (Fin.last r : Fin (r+1)) ≠ 0 := by
    intro h
    have he := congrArg (fun i : Fin (r+1) => i.val) h
    change r=0 at he
    omega
  have h := congrArg (fun M : Mat K r => M (0 : Fin (r+1)) (Fin.last r)) hc
  have hz : (1 : K)=0 := by
    simpa only [signedReversalUnit_apply,Fin.rev_zero,if_true,signWeight,
      Fin.val_zero,pow_zero,Matrix.smul_apply,Matrix.one_apply,
      if_neg (Ne.symm hlast),smul_zero] using h
  exact one_ne_zero hz

def shiftedWitness (q : CFSG.PrimePower) (s : ℕ) : CFSG.Models.TwistedA (s+3) q :=
  unitaryProjectiveCover q s (reversalFixed q (s+3))

theorem shiftedWitness_square (q : CFSG.PrimePower) (s : ℕ) : shiftedWitness q s ^ 2=1 := by
  change (unitaryProjectiveCover q s (reversalFixed q (s+3)))^2=1
  rw [pow_two,←map_mul]
  apply (unitaryProjectiveCover_kernel_iff_scalar q s _).mpr
  refine ⟨(-1 : q.Extension 2)^(s+3),?_⟩
  change (signedReversalUnit (q.Extension 2) (s+3) : Mat (q.Extension 2) (s+3)) *
    (signedReversalUnit (q.Extension 2) (s+3) : Mat (q.Extension 2) (s+3)) = _
  exact signedReversal_square_scalar (q.Extension 2) (s+3)

theorem shiftedWitness_ne_one (q : CFSG.PrimePower) (s : ℕ) : shiftedWitness q s ≠ 1 := by
  intro he
  have hs := (unitaryProjectiveCover_kernel_iff_scalar q s (reversalFixed q (s+3))).mp he
  change ∃ c : q.Extension 2,
    (signedReversalUnit (q.Extension 2) (s+3) : Mat (q.Extension 2) (s+3))=c • 1 at hs
  exact signedReversal_not_scalar (q.Extension 2) (s+3) (by omega) hs

theorem shifted_even_card (q : CFSG.PrimePower) (s : ℕ) :
    Even (Nat.card (CFSG.Models.TwistedA (s+3) q)) :=
  even_card_of_nontrivial_square (shiftedWitness q s)
    (shiftedWitness_square q s) (shiftedWitness_ne_one q s)

def rankTwoWitness (q : CFSG.PrimePower) (hq : 3≤q.order) : CFSG.Models.TwistedA 2 q :=
  rankTwoProjectiveCover q hq (reversalFixed q 2)

theorem rankTwoWitness_square (q : CFSG.PrimePower) (hq : 3≤q.order) :
    rankTwoWitness q hq ^ 2=1 := by
  have hi : (rankTwoWitness q hq)⁻¹=rankTwoWitness q hq :=
    rankTwoProjectiveWeyl_inv q hq
  calc
    _ = rankTwoWitness q hq * rankTwoWitness q hq := pow_two _
    _ = (rankTwoWitness q hq)⁻¹ * rankTwoWitness q hq :=
      congrArg (fun x => x * rankTwoWitness q hq) hi.symm
    _ = 1 := inv_mul_cancel _

theorem rankTwoWitness_ne_one (q : CFSG.PrimePower) (hq : 3≤q.order) :
    rankTwoWitness q hq ≠ 1 := by
  intro he
  apply rankTwoProjective_reversal_not_flag q hq
  change rankTwoWitness q hq ∈ (rankTwoUpperFlag q).map (rankTwoProjectiveCover q hq)
  rw [he]
  exact Subgroup.one_mem _

theorem rankTwo_even_card (q : CFSG.PrimePower) (hq : 3≤q.order) :
    Even (Nat.card (CFSG.Models.TwistedA 2 q)) :=
  even_card_of_nontrivial_square (rankTwoWitness q hq)
    (rankTwoWitness_square q hq) (rankTwoWitness_ne_one q hq)

theorem higher_even_card (r : ℕ) (hr : 3≤r) (q : CFSG.PrimePower) :
    Even (Nat.card (CFSG.Models.TwistedA r q)) := by
  cases r with
  | zero => omega
  | succ r =>
    cases r with
    | zero => omega
    | succ r =>
      cases r with
      | zero => omega
      | succ s => exact shifted_even_card q s

theorem twistedA_even_card (r : ℕ) (hr : 2≤r) (q : CFSG.PrimePower)
    (hsmall : r=2 → q.order≠2) : Even (Nat.card (CFSG.Models.TwistedA r q)) := by
  by_cases ht : r=2
  · subst r
    have htwo : 2≤q.order := q.prime_isPrime.two_le.trans
      (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
    exact rankTwo_even_card q (by have := hsmall rfl; omega)
  · exact higher_even_card r (by omega) q

end SymmetricSubgroupAsymptotics.CFSGTwistedAReversalEvenOrder
