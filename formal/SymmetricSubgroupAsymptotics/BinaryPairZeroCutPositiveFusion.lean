import SymmetricSubgroupAsymptotics.BinaryPairZeroCutFusion

/-! Zero cut also has a strictly positive original gap at pair exponents
nine and ten. These fixed widths may use finite direct decay without the
stronger margin used by the uniform wide aggregate. The capacity and
extension remain those of the original frame and normal subgroup. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

/-- The exact normalized middle width at nine propagates by Pascal's
doubling bound. This bound is strictly smaller than one quarter. -/
theorem binary_middle_le_sixtyThree_twoFiftySixth (k : ℕ) (hk : 9≤k) :
    256*k.choose (k/2)≤63*2^k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    calc
      256*(k+1).choose ((k+1)/2)≤256*(2*k.choose (k/2)) :=
        Nat.mul_le_mul_left 256 (binary_middle_succ_le_twice k)
      _ = 2*(256*k.choose (k/2)) := by ring
      _ ≤ 2*(63*2^k) := Nat.mul_le_mul_left 2 ih
      _ = 63*2^(k+1) := by rw [pow_succ]; ring

/-- A smaller positive gap already suffices for a fixed finite menu.
At physical widths 1024 and 2048 this gives e at least 1/2 and 1. -/
theorem binary_zeroCut_positive_gap (k : ℕ) (hk : 9≤k)
    (r : ℝ) (hr : r≤(k.choose (k/2) : ℝ)) :
    0<(2*(2:ℝ)^k-(2:ℝ)^k-4*r)/16 ∧
      (2*(2:ℝ)^k)/2048≤(2*(2:ℝ)^k-(2:ℝ)^k-4*r)/16 := by
  have hwidth : (256:ℝ)*(k.choose (k/2) : ℝ)≤63*(2:ℝ)^k := by
    exact_mod_cast binary_middle_le_sixtyThree_twoFiftySixth k hk
  have hp : 0<(2:ℝ)^k := pow_pos (by norm_num) _
  constructor <;> linarith

namespace BinaryPairFrame

variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U I) (N : Subgroup U) [N.Normal]

/-- Every original normal and every actual pair frame has the positive
zero-cut gap from physical width 1024 on. The moment and survival envelope
are the unchanged exact ones in BinaryPairZeroCutFusion. -/
theorem zeroCut_positive_parameters [Finite X] [Finite I]
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (k : ℕ) (hk : 9≤k) (hI : Nat.card I=2^k) :
    16*Nat.card I≤13*Nat.card X ∧ Nat.card I<Nat.card X ∧
      0<F.zeroCutGapParameter N ∧
      (Nat.card X : ℝ)/2048≤F.zeroCutGapParameter N := by
  letI : MulAction.IsPretransitive F.top.range I := F.top_pretransitive
  have hr := F.zeroCutCapacity_le N hU k hI
  have hgap := binary_zeroCut_positive_gap k hk (F.zeroCutCapacity N) hr
  have hX := F.card_points
  have hp : 0<2^k := pow_pos (by decide) _
  refine ⟨by rw [hX,hI]; omega,by rw [hX,hI]; omega,?_⟩
  simpa only [zeroCutGapParameter,hX,hI,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    using hgap

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
