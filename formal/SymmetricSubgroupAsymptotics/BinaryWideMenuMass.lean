import SymmetricSubgroupAsymptotics.BinaryPairFrameMenuMass
import SymmetricSubgroupAsymptotics.TransitiveBinaryActionCount
import SymmetricSubgroupAsymptotics.BinaryMenuExponentUniform

/-! Complete original binary menu mass at a fixed power degree. Each
actual action contributes every distinct realized pair system, one fixed
auxiliary chart per system, every original normal and every central cut.
The divisor is its original permutation normalizer. The action family is
separated by literal permutation conjugacy; no numerical menu bound is a
premise. This module does not assert local cut acceptance or a physical
cover of all subgroup owners. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Pointwise
namespace SymmetricSubgroupAsymptotics

variable {X : Type} [Finite X]

/-- The explicit natural exponent at original degree 2^(k+1). -/
def binaryWideMenuExponent (k : ℕ) : ℕ :=
  2*((2^(k+1)-1)*binaryCumulativeWidth (k+1)) +
    k.choose (k/2)*k.choose (k/2) +
    2^k*(1+binaryCumulativeWidth k) + 2^(k+1)

theorem binaryWideMenuExponent_cast (k : ℕ) :
    (binaryWideMenuExponent k : ℝ) = binaryMenuExponent (k+1) := by
  have hp : 1 ≤ (2 : ℕ)^(k+1) := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
  simp only [binaryWideMenuExponent, binaryMenuExponent, Nat.add_sub_cancel,
    Nat.cast_add, Nat.cast_mul, Nat.cast_sub hp, Nat.cast_pow,
    Nat.cast_one, Nat.cast_ofNat]
  rw [pow_succ]
  ring

/-- One chosen auxiliary frame for each distinct original pair system. -/
def binaryActionPairMenuMass (k : ℕ) (U : Subgroup (Equiv.Perm X)) : ℕ := by
  letI : Finite (RealizedPairing U (Fin (2^k))) := RealizedPairing.finite
  letI := Fintype.ofFinite (RealizedPairing U (Fin (2^k)))
  exact ∑ p : RealizedPairing U (Fin (2^k)), p.chosenFrame.frameMenuMass

theorem binaryActionPairMenuMass_le
    (k : ℕ) (U : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hdegree : Nat.card X = 2^(k+1)) :
    binaryActionPairMenuMass k U ≤
      2^(2^(k+1) + (2^(k+1)-1)*binaryCumulativeWidth (k+1) +
        k.choose (k/2)*k.choose (k/2) + 2^k*(1+binaryCumulativeWidth k)) := by
  classical
  letI : Finite (RealizedPairing U (Fin (2^k))) := RealizedPairing.finite
  letI := Fintype.ofFinite (RealizedPairing U (Fin (2^k)))
  letI : Nonempty X := (Nat.card_pos_iff.mp (by rw [hdegree]; positivity)).1
  let b := (2^(k+1)-1)*binaryCumulativeWidth (k+1) +
    k.choose (k/2)*k.choose (k/2) + 2^k*(1+binaryCumulativeWidth k)
  have hp : Nat.card (RealizedPairing U (Fin (2^k))) ≤ 2^(2^(k+1)) := by
    calc
      _ ≤ Nat.card X-1 := RealizedPairing.card_le_of_nonempty
      _ ≤ 2^(k+1) := by rw [hdegree]; omega
      _ ≤ 2^(2^(k+1)) := (Nat.lt_pow_self (by decide : 1 < 2)).le
  have hsum : binaryActionPairMenuMass k U ≤
      Nat.card (RealizedPairing U (Fin (2^k))) * 2^b := by
    change (∑ p : RealizedPairing U (Fin (2^k)), p.chosenFrame.frameMenuMass) ≤ _
    calc
      _ ≤ ∑ _p : RealizedPairing U (Fin (2^k)), 2^b := by
        apply Finset.sum_le_sum
        intro p _
        exact p.chosenFrame.frameMenuMass_le k hU hdegree (Nat.card_fin _)
      _ = _ := by simp [Nat.card_eq_fintype_card]
  calc
    _ ≤ 2^(2^(k+1))*2^b := hsum.trans (Nat.mul_le_mul_right _ hp)
    _ = _ := by rw [← pow_add]; congr 1; dsimp [b]; omega

/-- This is the original normalizer divisor, before any upper estimate. -/
def binaryOriginalWeightedMenuMass {ι : Type*} [Fintype ι]
    (k : ℕ) (actions : ι → Subgroup (Equiv.Perm X)) : ℝ :=
  ∑ i, (binaryActionPairMenuMass k (actions i) : ℝ) /
    (Nat.card (Subgroup.normalizer (actions i : Set (Equiv.Perm X))) : ℝ)

/-- Summing the actual action, frame, original normal and central-cut
costs gives an explicit bound, retaining the original divisor throughout. -/
theorem binaryOriginalWeightedMenuMass_le
    {ι : Type*} [Fintype ι] (k : ℕ) (P : Sylow 2 (Equiv.Perm X))
    (actions : ι → Subgroup (Equiv.Perm X))
    (htrans : ∀ i, MulAction.IsPretransitive (actions i) X)
    (hgroup : ∀ i, IsPGroup 2 (actions i))
    (hdegree : Nat.card X = 2^(k+1))
    (hsep : ∀ i j (c : Equiv.Perm X),
      MulAut.conj c • actions i = actions j → i=j) :
    binaryOriginalWeightedMenuMass k actions ≤ (2 : ℝ)^binaryWideMenuExponent k := by
  classical
  let a := (2^(k+1)-1)*binaryCumulativeWidth (k+1)
  let b := 2^(k+1)+a+k.choose (k/2)*k.choose (k/2)+
    2^k*(1+binaryCumulativeWidth k)
  have hcount : Nat.card ι ≤ 2^a :=
    transitiveBinary_action_family_card_le_degree (k+1) P actions htrans hgroup hdegree hsep
  have hmass (i : ι) : binaryActionPairMenuMass k (actions i) ≤ 2^b := by
    letI := htrans i
    exact binaryActionPairMenuMass_le k (actions i) (hgroup i) hdegree
  have hnat : (∑ i, binaryActionPairMenuMass k (actions i)) ≤
      2^binaryWideMenuExponent k := by
    calc
      _ ≤ ∑ _i : ι, 2^b := Finset.sum_le_sum (fun i _ => hmass i)
      _ = Nat.card ι * 2^b := by simp [Nat.card_eq_fintype_card]
      _ ≤ 2^a * 2^b := Nat.mul_le_mul_right _ hcount
      _ = _ := by rw [← pow_add]; congr 1; dsimp [a,b,binaryWideMenuExponent]; omega
  calc
    _ ≤ ∑ i, (binaryActionPairMenuMass k (actions i) : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      apply div_le_self (Nat.cast_nonneg _)
      exact_mod_cast (Nat.card_pos
        (α := Subgroup.normalizer (actions i : Set (Equiv.Perm X))))
    _ ≤ (2 : ℝ)^binaryWideMenuExponent k := by exact_mod_cast hnat

/-- One constant is valid simultaneously for every power degree and
every conjugacy-separated actual action family. All original divisors,
normals and central-cut cohomology fibres occur in the defined left side. -/
theorem binaryOriginalWeightedMenuMass_uniform_le :
    ∃ H : ℝ, 0 ≤ H ∧
      ∀ {X : Type} [Finite X] {ι : Type} [Fintype ι]
        (k : ℕ) (P : Sylow 2 (Equiv.Perm X))
        (actions : ι → Subgroup (Equiv.Perm X))
        (htrans : ∀ i, MulAction.IsPretransitive (actions i) X)
        (hgroup : ∀ i, IsPGroup 2 (actions i))
        (hdegree : Nat.card X = 2^(k+1))
        (hsep : ∀ i j (c : Equiv.Perm X),
          MulAut.conj c • actions i = actions j → i=j),
        binaryOriginalWeightedMenuMass k actions ≤
          (2 : ℝ)^(((2 : ℝ)^(k+1))^2/128+H) := by
  obtain ⟨H,hH,hbound⟩ := binaryMenuExponent_uniform_le_one128
  refine ⟨H,hH,?_⟩
  intro X _ ι _ k P actions htrans hgroup hdegree hsep
  apply (binaryOriginalWeightedMenuMass_le k P actions htrans hgroup hdegree hsep).trans
  rw [← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  rw [binaryWideMenuExponent_cast]
  exact hbound (k+1)

end SymmetricSubgroupAsymptotics
