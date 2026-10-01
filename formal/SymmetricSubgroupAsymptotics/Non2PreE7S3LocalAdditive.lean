import SymmetricSubgroupAsymptotics.Non2PreE7SaprimExceptionalOdd

/-!
# The three fixed local-S3 additive owners

`S3TWO`, `S3CYCL`, and `S3SYL` have one common formal shape.  Their audited
finite all-normal theorems give

`Z_J(U) ≤ B·Z_J(Q) + C·2^(θb)`

for one faithfully represented comparator `Q`.  The historical parameters
are `(w,v,θ)=(12,10,log₂(3)/3)`, `(9,6,log₂(3)/3)`, and
`(9,6,log₂(3)/2)`, respectively.  This module proves once that such a
complete same-source envelope supplies every literal normal axis, verifies
the three transfer windows, and sums the finite coefficients required by the
T1 numerical catalogue.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

private abbrev NormalAxis {w : ℕ} (i : PreE7NonPairActionClass w) :=
  {N : Subgroup (preE7NonPairAction w i) // N.Normal}

/-- The three exact local-S3 additive certificate shapes. -/
inductive PreE7S3LocalAdditiveKind
  | two
  | cyclic
  | sylow
  deriving DecidableEq, Fintype

def PreE7S3LocalAdditiveKind.family :
    PreE7S3LocalAdditiveKind → PreE7NoPairNoC3EarlierOwnerFamily
  | .two => .s3two
  | .cyclic => .s3cycl
  | .sylow => .s3syl

def PreE7S3LocalAdditiveKind.width : PreE7S3LocalAdditiveKind → ℕ
  | .two => 12
  | .cyclic | .sylow => 9

def PreE7S3LocalAdditiveKind.comparatorDegree :
    PreE7S3LocalAdditiveKind → ℕ
  | .two => 10
  | .cyclic | .sylow => 6

def PreE7S3LocalAdditiveKind.tailSlope :
    PreE7S3LocalAdditiveKind → ℝ
  | .two | .cyclic => Real.logb 2 3 / 3
  | .sylow => Real.logb 2 3 / 2

/-- One actual retained action carrying the exact audited complete envelope
for its fixed local-S3 branch.  `Q` is stored as an actual permutation
subgroup, so its faithful action is literal rather than an abstract promise. -/
structure PreE7S3LocalAdditiveSource
    (kind : PreE7S3LocalAdditiveKind)
    (w : ℕ) (i : PreE7NonPairActionClass w) : Type where
  width_eq : w = kind.width
  Q : Subgroup (Equiv.Perm (Fin kind.comparatorDegree))
  B : ℝ
  C : ℝ
  B_nonneg : 0 ≤ B
  C_nonneg : 0 ≤ C
  complete_bound : ∀ {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))),
    completeQuotientWeight (R := preE7NonPairAction w i) J ≤
      B * completeQuotientWeight (R := Q) J +
        C * (2 : ℝ) ^ (kind.tailSlope * b)
  main_menu : ∀ b,
    (Nat.card (NormalAxis i) : ℝ) * B ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)
  tail_menu : ∀ b,
    (Nat.card (NormalAxis i) : ℝ) * C ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)

namespace PreE7S3LocalAdditiveSource

variable {kind : PreE7S3LocalAdditiveKind}
  {w : ℕ} {i : PreE7NonPairActionClass w}
  (S : PreE7S3LocalAdditiveSource kind w i)

include S in
private theorem comparator_window :
    preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) -
        ((max 2 kind.comparatorDegree : ℕ) : ℝ)) / 8 := by
  rw [S.width_eq]
  cases kind <;>
    norm_num [PreE7S3LocalAdditiveKind.width,
      PreE7S3LocalAdditiveKind.comparatorDegree,
      preE7CharacterRho, evenWidth, halfDegree]

private theorem logThreeHalf_le_window_nine :
    Real.logb 2 3 / 2 ≤ preE7CharacterWindow 9 := by
  have hlog : 5 * Real.logb 2 3 < 8 := by
    have hp : ((3 : ℝ) ^ 5) < (2 : ℝ) ^ (8 : ℕ) := by norm_num
    have h := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
      (pow_pos (by norm_num) 5) hp
    simpa [Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using h
  norm_num [preE7CharacterWindow, preE7CharacterRho, halfDegree]
  linarith

include S in
private theorem tail_window :
    kind.tailSlope ≤ preE7CharacterWindow w := by
  rw [S.width_eq]
  cases kind with
  | two =>
      exact logThreeThird_le_window (by
        norm_num [PreE7S3LocalAdditiveKind.width])
  | cyclic =>
      exact logThreeThird_le_window (by
        norm_num [PreE7S3LocalAdditiveKind.width])
  | sylow =>
      exact logThreeHalf_le_window_nine

/-- A complete all-normal bound dominates each one of its literal axes. -/
def axis (N : NormalAxis i) :
    PreE7SmallAxisCertificate (preE7NonPairAction w i) N S.Q kind.tailSlope := by
  refine .bounded S.B S.C S.B_nonneg S.C_nonneg ?_
  intro b J _
  exact (card_groupEpimorphism_le_completeQuotientWeight J N (MulEquiv.refl _)).trans
    (S.complete_bound J)

def toData : PreE7SmallAdditiveData w i where
  R := S.Q
  degree := kind.comparatorDegree
  action := S.Q.subtype
  action_injective := Subtype.val_injective
  tailSlope := kind.tailSlope
  comparator_window := S.comparator_window
  tail_window := S.tail_window
  axis := S.axis

private theorem axis_mainCoefficient (N : NormalAxis i) :
    (S.axis N).mainCoefficient = S.B := by
  simp [axis, PreE7SmallAxisCertificate.mainCoefficient]

private theorem axis_tailCoefficient (N : NormalAxis i) :
    (S.axis N).tailCoefficient = S.C := by
  simp [axis, PreE7SmallAxisCertificate.tailCoefficient]

/-- Complete numerical data for any of the three local-S3 additive owners. -/
noncomputable def numericalData :
    PreE7SmallAdditiveNumericalData kind.family w i where
  data := S.toData
  main_total_bound := by
    intro b
    unfold fusionAxisEnvelopeTotal
    calc
      (∑ N : NormalAxis i, ((S.toData).certificate kind.family).C b N) =
          (Nat.card (NormalAxis i) : ℝ) * S.B := by
        simp_rw [show ∀ N : NormalAxis i,
          ((S.toData).certificate kind.family).C b N = S.B from
            fun N => S.axis_mainCoefficient N]
        simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := S.main_menu b
  tail_total_bound := by
    intro b
    unfold fusionAxisEnvelopeTotal
    calc
      (∑ N : NormalAxis i,
          ((S.toData).certificate kind.family).tailCoefficient b N) =
          (Nat.card (NormalAxis i) : ℝ) * S.C := by
        simp_rw [show ∀ N : NormalAxis i,
          ((S.toData).certificate kind.family).tailCoefficient b N = S.C from
            fun N => S.axis_tailCoefficient N]
        simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := S.tail_menu b

end PreE7S3LocalAdditiveSource

abbrev PreE7S3TwoSource := PreE7S3LocalAdditiveSource .two
abbrev PreE7S3CyclicSource := PreE7S3LocalAdditiveSource .cyclic
abbrev PreE7S3SylowSource := PreE7S3LocalAdditiveSource .sylow

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
