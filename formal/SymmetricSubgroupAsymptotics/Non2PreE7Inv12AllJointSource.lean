import SymmetricSubgroupAsymptotics.Non2PreE7CompleteSourceRankTailBridge
import SymmetricSubgroupAsymptotics.Non2PreE7PaddedCertificateNumerics
import SymmetricSubgroupAsymptotics.TernaryThreeGroupEpiRecurrence
import SymmetricSubgroupAsymptotics.FusionCarrierIncidence
import SymmetricSubgroupAsymptotics.BinaryAbelianization

/-!
# The joint binary/ternary source theorem for INV12all

The degree-twelve INV12all row cannot be obtained by maximizing its binary
lift rank and ternary top rank independently.  This file retains one common
support parameter `c` on the literal source `J`.  It is used simultaneously
in

`4 d₃(J) ≤ b + c`,

and, for every literal normal quotient and every onto map to its degree-nine
ternary top,

`2 d₂(ker θ) + 3 c ≤ b`.

Every normal axis also retains its actual projection onto a transitive
degree-nine `3`-group and the fibres of that projection.  Thus the theorem
below combines the top and lift counts before discarding `c`; it never
multiplies two unrelated worst-case estimates.  The rational envelope
`3^x ≤ 2^(8x/5)` gives the audited binary slope `43/30`.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

universe u

/-- One literal INV12 quotient axis.  The top is the actual transitive
degree-nine `3`-group.  The fibre estimate is the regular-module lift theorem
after the binary kernel module and its (at most six-dimensional) finite
cohomology factor have been retained. -/
structure PreE7Inv12JointAxis (Q : Type u) [Group Q] [Finite Q] : Type (u + 1) where
  Top : Subgroup (Equiv.Perm (Fin 9))
  top_pretransitive : MulAction.IsPretransitive Top (Fin 9)
  top_isPGroup : IsPGroup 3 Top
  projection : Q →* Top
  projection_surjective : Function.Surjective projection
  fibre_bound : ∀ {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b)))
    (theta : GroupEpimorphism J Top),
    Nat.card {f : GroupEpimorphism J Q //
      (⟨projection.comp f.1, projection_surjective.comp f.2⟩ :
        GroupEpimorphism J Top) = theta} ≤
        64 * 2 ^ binaryCharacterRank theta.1.ker

namespace PreE7Inv12JointAxis

variable {Q : Type*} [Group Q] [Finite Q]
  (A : PreE7Inv12JointAxis Q)

/-- Compose an onto quotient map with the retained degree-nine top. -/
def topMap {b : ℕ} {J : Subgroup (Equiv.Perm (Fin b))} :
    GroupEpimorphism J Q → GroupEpimorphism J A.Top := fun f =>
  ⟨A.projection.comp f.1, A.projection_surjective.comp f.2⟩

/-- The degree-nine recurrence supplies one constant for this actual top,
uniformly in the source degree and in every quotient target. -/
noncomputable def topConstant : ℝ := by
  letI : MulAction.IsPretransitive A.Top (Fin 9) := A.top_pretransitive
  exact Classical.choose
    (degreeNine_quotientCharacterEnvelope A.Top (by simp) A.top_isPGroup)

theorem topConstant_nonneg : 0 ≤ A.topConstant := by
  letI : MulAction.IsPretransitive A.Top (Fin 9) := A.top_pretransitive
  exact (Classical.choose_spec
    (degreeNine_quotientCharacterEnvelope A.Top (by simp) A.top_isPGroup)).1

theorem topEnvelope :
    TernaryQuotientCharacterEnvelope A.Top (1 / 3 : ℝ) A.topConstant := by
  letI : MulAction.IsPretransitive A.Top (Fin 9) := A.top_pretransitive
  have hs : 0 ≤ A.topConstant ∧
      TernaryQuotientCharacterEnvelope A.Top (1 / 3 : ℝ) A.topConstant :=
    Classical.choose_spec
      (degreeNine_quotientCharacterEnvelope A.Top (by simp) A.top_isPGroup)
  intro Q' _ _ q hq b J
  exact hs.2 (Q := Q') q hq b J

/-- The elementary arithmetic behind the joint row.  Its hypotheses are
kept integral because they arise from literal orbit counts and character
ranks. -/
theorem joint_exponent_le
    {b c d₂ d₃ : ℕ}
    (hbinary : 2 * d₂ + 3 * c ≤ b)
    (hternary : 4 * d₃ ≤ b + c) :
    (d₂ : ℝ) + (8 / 5 : ℝ) * ((d₃ : ℝ) + (b : ℝ) / 3) ≤
      (43 / 30 : ℝ) * b := by
  have hbinaryR : (2 : ℝ) * d₂ + 3 * c ≤ b := by exact_mod_cast hbinary
  have hternaryR : (4 : ℝ) * d₃ ≤ b + c := by exact_mod_cast hternary
  nlinarith

/-- One normal quotient is bounded only after its degree-nine top count and
all binary lift fibres have been combined with the same support `c`. -/
theorem epimorphism_card_le
    {b c : ℕ} (J : Subgroup (Equiv.Perm (Fin b)))
    (hc : 3 * c ≤ b)
    (hternary : 4 * Module.finrank (ZMod 3) (PrimeCharacters 3 J) ≤ b + c)
    (hbinary : ∀ theta : GroupEpimorphism J A.Top,
      2 * binaryCharacterRank theta.1.ker + 3 * c ≤ b) :
    (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
      (64 * A.topConstant) * (2 : ℝ) ^ ((43 / 30 : ℝ) * b) := by
  let d₃ := Module.finrank (ZMod 3) (PrimeCharacters 3 J)
  have htop := A.topEnvelope (MonoidHom.id A.Top) Function.surjective_id b J
  have hcR : (3 : ℝ) * c ≤ b := by exact_mod_cast hc
  have hfibres :
      (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
        (Nat.card (GroupEpimorphism J A.Top) : ℝ) *
          (64 * (2 : ℝ) ^ (((b : ℝ) - 3 * c) / 2)) := by
    have hcard : Nat.card (GroupEpimorphism J Q) =
        Nat.card (Σ theta : GroupEpimorphism J A.Top,
          {f : GroupEpimorphism J Q // A.topMap f = theta}) :=
      (Nat.card_congr (Equiv.sigmaFiberEquiv A.topMap)).symm
    rw [hcard, Nat.card_sigma, Nat.cast_sum]
    calc
      ∑ theta : GroupEpimorphism J A.Top,
          (Nat.card {f : GroupEpimorphism J Q // A.topMap f = theta} : ℝ) ≤
          ∑ _theta : GroupEpimorphism J A.Top,
            64 * (2 : ℝ) ^ (((b : ℝ) - 3 * c) / 2) := by
        apply Finset.sum_le_sum
        intro theta _
        have hfb := A.fibre_bound J theta
        have hrankR : (binaryCharacterRank theta.1.ker : ℝ) ≤
            ((b : ℝ) - 3 * c) / 2 := by
          have h := hbinary theta
          have hR : (2 : ℝ) * binaryCharacterRank theta.1.ker + 3 * c ≤ b := by
            exact_mod_cast h
          linarith
        have hpow := Real.rpow_le_rpow_of_exponent_le
          (by norm_num : (1 : ℝ) ≤ 2) hrankR
        have hfbR :
            (Nat.card {f : GroupEpimorphism J Q // A.topMap f = theta} : ℝ) ≤
              64 * (2 : ℝ) ^ (binaryCharacterRank theta.1.ker : ℝ) := by
          exact_mod_cast hfb
        exact hfbR.trans (mul_le_mul_of_nonneg_left hpow (by norm_num))
      _ = (Nat.card (GroupEpimorphism J A.Top) : ℝ) *
          (64 * (2 : ℝ) ^ (((b : ℝ) - 3 * c) / 2)) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Fintype.card_eq_nat_card]
  have hthree :
      (3 : ℝ) ^ ((d₃ : ℝ) + (1 / 3 : ℝ) * b) ≤
        (2 : ℝ) ^ ((8 / 5 : ℝ) * ((d₃ : ℝ) + (b : ℝ) / 3)) := by
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using
      (c1_ternary_rpow_envelope
        (x := (d₃ : ℝ) + (b : ℝ) / 3) (by positivity))
  calc
    (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
        (Nat.card (GroupEpimorphism J A.Top) : ℝ) *
          (64 * (2 : ℝ) ^ (((b : ℝ) - 3 * c) / 2)) := hfibres
    _ ≤ (A.topConstant *
          (3 : ℝ) ^ ((d₃ : ℝ) + (1 / 3 : ℝ) * b)) *
          (64 * (2 : ℝ) ^ (((b : ℝ) - 3 * c) / 2)) :=
      mul_le_mul_of_nonneg_right htop (by positivity)
    _ ≤ (A.topConstant *
          (2 : ℝ) ^ ((8 / 5 : ℝ) * ((d₃ : ℝ) + (b : ℝ) / 3))) *
          (64 * (2 : ℝ) ^ (((b : ℝ) - 3 * c) / 2)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hthree A.topConstant_nonneg) (by positivity)
    _ = (64 * A.topConstant) *
          ((2 : ℝ) ^ (((b : ℝ) - 3 * c) / 2) *
            (2 : ℝ) ^ ((8 / 5 : ℝ) * ((d₃ : ℝ) + (b : ℝ) / 3))) := by
      ring
    _ = (64 * A.topConstant) * (2 : ℝ) ^
          ((((b : ℝ) - 3 * c) / 2) +
            (8 / 5 : ℝ) * ((d₃ : ℝ) + (b : ℝ) / 3)) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    _ ≤ (64 * A.topConstant) * (2 : ℝ) ^ ((43 / 30 : ℝ) * b) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) A.topConstant_nonneg)
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hternaryR : (4 : ℝ) * d₃ ≤ b + c := by
        exact_mod_cast hternary
      dsimp only [d₃] at hternaryR ⊢
      nlinarith

end PreE7Inv12JointAxis

/-- The actual INV12all predicate on a retained degree-twelve action.  The
same `c` controls every normal axis and every top epimorphism. -/
structure PreE7Inv12AllSource
    (w : ℕ) (i : PreE7NonPairActionClass w) : Type 1 where
  width_eq : w = 12
  axis : ∀ N : {N : Subgroup (preE7NonPairAction w i) // N.Normal},
    PreE7Inv12JointAxis (preE7NonPairAction w i ⧸ N.1)
  joint_support : ∀ {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))),
    ∃ c : ℕ, 3 * c ≤ b ∧
      4 * Module.finrank (ZMod 3) (PrimeCharacters 3 J) ≤ b + c ∧
      ∀ (N : {N : Subgroup (preE7NonPairAction w i) // N.Normal})
        (theta : GroupEpimorphism J (axis N).Top),
        2 * binaryCharacterRank theta.1.ker + 3 * c ≤ b
  coefficient_menu : ∀ b,
    (∑ N ∈ (@Finset.univ
        {N : Subgroup (preE7NonPairAction w i) // N.Normal}
        (Subtype.fintype Subgroup.Normal)),
      64 * (axis N).topConstant) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)

namespace PreE7Inv12AllSource

variable {w : ℕ} {i : PreE7NonPairActionClass w}
  (S : PreE7Inv12AllSource w i)

def coefficient : ℝ :=
  ∑ N ∈ (@Finset.univ
      {N : Subgroup (preE7NonPairAction w i) // N.Normal}
      (Subtype.fintype Subgroup.Normal)),
    64 * (S.axis N).topConstant

theorem coefficient_nonneg : 0 ≤ S.coefficient := by
  unfold coefficient
  exact Finset.sum_nonneg (fun N _ =>
    mul_nonneg (by norm_num) (S.axis N).topConstant_nonneg)

/-- The complete all-normal epimorphism sum has slope `43/30`.  The support
parameter is chosen once, outside the normal-axis sum. -/
theorem completeQuotientWeight_le
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := preE7NonPairAction w i) J ≤
      S.coefficient * (2 : ℝ) ^ ((43 / 30 : ℝ) * b) := by
  obtain ⟨c, hc, hternary, hbinary⟩ := S.joint_support J
  unfold completeQuotientWeight completeQuotientCount coefficient
  rw [Nat.cast_sum]
  calc
    (∑ N ∈ (@Finset.univ
        {N : Subgroup (preE7NonPairAction w i) // N.Normal}
        (Subtype.fintype Subgroup.Normal)),
        (Nat.card (GroupEpimorphism J
          (preE7NonPairAction w i ⧸ N.1)) : ℝ)) ≤
        (∑ N ∈ (@Finset.univ
          {N : Subgroup (preE7NonPairAction w i) // N.Normal}
          (Subtype.fintype Subgroup.Normal)),
          (64 * (S.axis N).topConstant) *
            (2 : ℝ) ^ ((43 / 30 : ℝ) * b)) := by
      apply Finset.sum_le_sum
      intro N _
      exact (S.axis N).epimorphism_card_le J hc hternary (hbinary N)
    _ = ((∑ N ∈ (@Finset.univ
          {N : Subgroup (preE7NonPairAction w i) // N.Normal}
          (Subtype.fintype Subgroup.Normal)),
          64 * (S.axis N).topConstant)) *
            (2 : ℝ) ^ ((43 / 30 : ℝ) * b) := by
      rw [Finset.sum_mul]

def degree (_T : PreE7Inv12AllSource w i) : ℕ :=
  paddedComparatorDegree preE7CharacterRho 2 w

def delta (_T : PreE7Inv12AllSource w i) : ℝ :=
  paddedComparatorDelta preE7CharacterRho 0 2 w

def cutoff : ℝ := (S.degree : ℝ) / 8 + S.delta / 2

def alpha : ℝ := S.cutoff

theorem entryParameters :
    PreE7CharacterEntryParameters preE7CharacterRho w S.degree 0 S.delta
      S.cutoff S.alpha (43 / 30 : ℝ) := by
  have hmargin : preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - 2) / 8 - 0 := by
    rw [S.width_eq]
    norm_num [preE7CharacterRho, evenWidth, halfDegree]
  have htail : (43 / 30 : ℝ) ≤ preE7CharacterWindow w := by
    rw [S.width_eq]
    norm_num [preE7CharacterWindow, preE7CharacterRho, halfDegree]
  simpa [degree, delta, cutoff, alpha] using
    (preE7Padded_entryParameters_withTail
      (w := w) (v0 := 2) (eta := (0 : ℝ)) (theta := (43 / 30 : ℝ))
      (by norm_num) (by norm_num) hmargin htail)

/-- INV12all as a direct complete-source certificate with trivial
comparator. -/
noncomputable def certificate :
    PreE7CompleteSourceComparatorCertificate .inv12All w i where
  R := PUnit
  groupR := inferInstance
  finiteR := inferInstance
  v := S.degree
  action := 1
  action_injective := fun _ _ _ => Subsingleton.elim _ _
  D := fun _ => 0
  T := fun _ => S.coefficient
  eta := 0
  delta := S.delta
  cutoff := S.cutoff
  alpha := S.alpha
  theta := 43 / 30
  alpha_eq := by simp [alpha]
  D_nonneg := fun _ => le_rfl
  T_nonneg := fun _ => S.coefficient_nonneg
  broad_source_envelope := by
    intro b J
    rw [completeQuotientWeight_eq_one_of_subsingleton (R := PUnit) J]
    have hforget :
        fusionCompleteSourceSum (preE7NonPairAction w i)
            (preE7NoPairNoC3BroadActionPredicate w i b) J ≤
          completeQuotientWeight (R := preE7NonPairAction w i) J := by
      unfold fusionCompleteSourceSum completeQuotientWeight completeQuotientCount
      rw [Nat.cast_sum]
      exact Finset.sum_le_sum (fun N _ =>
        fusionSurvivingEpiCount_le_groupEpimorphism_card
          (preE7NonPairAction w i)
          (preE7NoPairNoC3BroadActionPredicate w i b) N J)
    calc
      fusionCompleteSourceSum (preE7NonPairAction w i)
          (preE7NoPairNoC3BroadActionPredicate w i b) J ≤
          completeQuotientWeight (R := preE7NonPairAction w i) J := hforget
      _ ≤ S.coefficient * (2 : ℝ) ^ ((43 / 30 : ℝ) * b) :=
        S.completeQuotientWeight_le J
      _ = (0 * (2 : ℝ) ^ ((0 : ℝ) * b)) * 1 +
          S.coefficient * (2 : ℝ) ^ ((43 / 30 : ℝ) * b) := by ring

noncomputable def numericalData :
    PreE7CompleteSourceNumericalData .inv12All w i where
  certificate := S.certificate
  parameters := S.entryParameters
  main_total_bound := fun _ => by positivity
  tail_total_bound := S.coefficient_menu

/-- The complete INV12all predicate enters the final source catalogue. -/
noncomputable def toRankTailOwnerSource :
    PreE7RankTailOwnerSourceData w i :=
  .ordinary .inv12All (.completeSource S.numericalData)

end PreE7Inv12AllSource

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
