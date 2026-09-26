import SymmetricSubgroupAsymptotics.BinaryStructuredEpimorphisms

/-! The explicit structured count in the polynomial-times-exponential form
used by the carrier recurrence. Its positive constant depends only on the
actual target. Both exponential coefficients are exact binary order logs.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- An explicit target-only constant; a finite target alphabet can take
the maximum of these constants without imposing any bound on source order. -/
def binaryStructuredEpiConstant (Q : Type*) [Group Q] [Finite Q] : ℕ :=
  max (Nat.log 2 (Nat.card Q))
    ((Nat.card Q)^((Nat.card (commutator Q))^(Nat.log 2 (Nat.card Q))))

theorem binaryStructuredEpiConstant_pos (Q : Type*) [Group Q] [Finite Q] :
    0 < binaryStructuredEpiConstant Q :=
  lt_of_lt_of_le (pow_pos (Nat.card_pos : 0 < Nat.card Q) _) (le_max_right _ _)

private theorem binaryStructured_card_eq_pow_log
    {Q : Type*} [Group Q] [Finite Q] (hQ : IsPGroup 2 Q) :
    Nat.card Q = 2^(Nat.log 2 (Nat.card Q)) := by
  obtain ⟨a,ha⟩ := hQ.exists_card_eq
  rw [ha,Nat.log_pow (by decide)]

/-- The actual finite binary source satisfies the structured epimorphism
bound with a proved target-only polynomial factor. No numerical epimorphism
estimate, nilpotency-class limit, or conjugacy-class hypothesis is assumed. -/
theorem binaryStructured_epimorphism_card_le_polynomial
    {G Q : Type*} [Group G] [Group Q] [Finite G] [Finite Q]
    (hG : IsPGroup 2 G) (hQ : IsPGroup 2 Q) :
    Nat.card {f : G →* Q // Function.Surjective f} ≤
      binaryStructuredEpiConstant Q *
        (binaryCharacterRank G + 2)^(binaryStructuredEpiConstant Q) *
        2^(Nat.log 2 (Nat.card (Subgroup.center Q)) * binaryCharacterRank G +
          Nat.log 2 (Nat.card (commutator Q)) * primeDerivedNormalRank 2 G) := by
  let d := binaryCharacterRank G
  let r := primeDerivedNormalRank 2 G
  let q := Nat.log 2 (Nat.card Q)
  let a := (Nat.card Q)^((Nat.card (commutator Q))^q)
  let C := binaryStructuredEpiConstant Q
  have ha : a ≤ C := le_max_right _ _
  have hq : q ≤ C := le_max_left _ _
  have hpoly : (d+1)^q ≤ (d+2)^C := by
    calc
      _ ≤ (d+2)^q := pow_le_pow_left₀ (Nat.zero_le _)
        (Nat.succ_le_succ (Nat.le_succ d)) q
      _ ≤ _ := Nat.pow_le_pow_right (Nat.zero_lt_succ (d+1)) hq
  have hslope : (Nat.card (commutator Q))^r *
      (Nat.card (Subgroup.center Q))^d =
      2^(Nat.log 2 (Nat.card (Subgroup.center Q))*d +
        Nat.log 2 (Nat.card (commutator Q))*r) := by
    have hc : (Nat.card (commutator Q))^r =
        2^(Nat.log 2 (Nat.card (commutator Q))*r) :=
      (congrArg (fun n : ℕ => n^r)
        (binaryStructured_card_eq_pow_log (hQ.to_subgroup (commutator Q)))).trans
        (pow_mul 2 _ _).symm
    have hz : (Nat.card (Subgroup.center Q))^d =
        2^(Nat.log 2 (Nat.card (Subgroup.center Q))*d) :=
      (congrArg (fun n : ℕ => n^d)
        (binaryStructured_card_eq_pow_log (hQ.to_subgroup (Subgroup.center Q)))).trans
        (pow_mul 2 _ _).symm
    rw [hc,hz,← pow_add,Nat.add_comm]
  calc
    _ ≤ (d+1)^q * ((Nat.card (commutator Q))^r *
        (a*(Nat.card (Subgroup.center Q))^d)) :=
      binaryStructured_epimorphism_card_le hG hQ
    _ = a*(d+1)^q * ((Nat.card (commutator Q))^r *
        (Nat.card (Subgroup.center Q))^d) := by ac_rfl
    _ ≤ C*(d+2)^C * ((Nat.card (commutator Q))^r *
        (Nat.card (Subgroup.center Q))^d) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul ha hpoly)
    _ = _ := by rw [hslope]

end SymmetricSubgroupAsymptotics
