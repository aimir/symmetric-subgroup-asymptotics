import SymmetricSubgroupAsymptotics.BinaryTransitivePowerSevenCriterion
import SymmetricSubgroupAsymptotics.BinaryOrderSevenCharacterFusion
import SymmetricSubgroupAsymptotics.BinaryTransitivePowerBoundaryFusion

/-!
# Power-boundary sources at the proved-from-base binary class rate

All original normal axes are covered. Small source orders and nontrivial
normal quotients use the existing exact order certificates. The remaining
bottom axis uses a newly proved 5^(2/7) criterion from the actual original
central rank. No old 38/25 certificate is converted or assumed sufficient.
Only the actual binary permutation class theorem remains a named input
to the counting consumer in this narrow source.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryTransitivePowerSevenBoundary

open BinaryTransitivePowerBoundaryFusion

section Selection

variable {w : ℕ} (k : ℕ) (hk : 4≤k)
    (U : Subgroup (Equiv.Perm (Fin w)))
    [MulAction.IsPretransitive U (Fin w)] (hdegree : w=2^k)

/-- Only the width numeral and quotientBot change; the original action
supplies the actual central-involution cardinality throughout. -/
def botCriterionOfDegree (hlarge : 2^k<Nat.card U) :
    BinarySevenCharacterCriterion (U⧸(⊥:Subgroup U)) w := by
  have hw : 0<w := by rw [hdegree]; exact pow_pos (by decide : 0<2) _
  letI : Nonempty (Fin w) := ⟨⟨0,hw⟩⟩
  let C := (binaryTransitivePower_sevenCharacterCriterion (G := U) (X := Fin w)
    k hk (by simpa only [Nat.card_fin] using hdegree) hlarge).transport
      (QuotientGroup.quotientBot (G := U)).symm
  exact {
    dimension := C.dimension
    cardinal := C.cardinal
    gap := by simpa only [hdegree] using C.gap }

/-- Complete original-normal selection, fixed before any exterior data. -/
def selectionOfDegree (hcard : Nat.card U≤2^(2^(k-1))) :
    BinaryOrderSevenCharacterSelection U := by
  rintro ⟨N,hNormal⟩
  letI := hNormal
  have hgap : 2*(2^(k-1)-1)<w := by
    rw [hdegree]
    exact order_marker_gap k (by omega)
  by_cases hsmall : Nat.card U≤2^(2^(k-1)-1)
  · exact .inl (BinaryOrderPrunedCoverage.certificateOfCard U N hsmall hgap)
  · by_cases hN : N=⊥
    · subst N
      have hlarge : 2^k<Nat.card U :=
        (degree_le_order_threshold k hk).trans_lt (Nat.lt_of_not_ge hsmall)
      exact .inr (botCriterionOfDegree k hk U hdegree hlarge)
    · have hhalf : 1≤2^(k-1) := Nat.one_le_pow _ _ (by decide)
      have hcard' : Nat.card U≤2^((2^(k-1)-1)+1) := by
        simpa only [Nat.sub_add_cancel hhalf] using hcard
      exact .inl (BinaryOrderPrunedNontrivialAxes.certificateOfNontrivial
        U N hcard' hN hgap)

theorem selectionOfDegree_prefixDegree_le (hcard : Nat.card U≤2^(2^(k-1)))
    (N : {N : Subgroup U // N.Normal}) :
    (selectionOfDegree k hk U hdegree hcard).prefixDegree N ≤ 2*(2^(k-1)-1) := by
  change ((selectionOfDegree k hk U hdegree hcard) N).prefixDegree ≤ _
  cases hC : (selectionOfDegree k hk U hdegree hcard) N with
  | inl C =>
      change 2*Nat.log 2 (Nat.card (U⧸N.1)) ≤ _
      have hg := C.gap
      have hw := two_mul_half k (by omega)
      omega
  | inr C => exact Nat.zero_le _

end Selection

def selection (k : ℕ) (hk : 4≤k)
    (U : Subgroup (Equiv.Perm (Fin (2^k))))
    [MulAction.IsPretransitive U (Fin (2^k))]
    (hcard : Nat.card U≤2^(2^(k-1))) : BinaryOrderSevenCharacterSelection U :=
  selectionOfDegree k hk U rfl hcard

section Physical

variable {h : ℕ} (k : ℕ) (hk : 4≤k)
    (U : Subgroup (Equiv.Perm (Fin (2*h))))
    [MulAction.IsPretransitive U (Fin (2*h))]
    (hdegree : 2*h=2^k) (hcard : Nat.card U≤2^(2^(k-1)))

theorem original_envelope (hclass : BinarySevenPermutationClassInput)
    (hU : IsPGroup 2 U) (b : ℕ)
    (P : Subgroup (U×Equiv.Perm (Fin b)) → Prop)
    (N : {N : Subgroup U // N.Normal}) (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount U P N J ≤
      fusionLocalFactor b h ((selectionOfDegree k hk U hdegree hcard).prefixDegree N)
        ((selectionOfDegree k hk U hdegree hcard).liftConstant N)
        ((selectionOfDegree k hk U hdegree hcard).gapParameter N)*
          (selectionOfDegree k hk U hdegree hcard).momentWeight N J :=
  (selectionOfDegree k hk U hdegree hcard).original_envelope hclass hU b P N J

/-- Direct first-moment physical bound, with the original action normalizer.
The only class input is the separate actual binary permutation theorem. -/
theorem direct_physical_bound (hclass : BinarySevenPermutationClassInput)
    (hU : IsPGroup 2 U) (b : ℕ)
    (P : Subgroup (U×Equiv.Perm (Fin b)) → Prop) (hP : FusionOrbitNatural U P) :
    (Nat.card (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)):ℝ)/
      exactBenchmark (b+2*h) ≤
      ∑ N : {N : Subgroup U // N.Normal},
        fusionDirectKernel b h ((selectionOfDegree k hk U hdegree hcard).prefixDegree N)
          ((selectionOfDegree k hk U hdegree hcard).liftConstant N)
          (Nat.card (Subgroup.normalizer (U : Set (Equiv.Perm (Fin (2*h))))):ℝ)
          ((selectionOfDegree k hk U hdegree hcard).gapParameter N)*
          ((subgroupCount (b+(selectionOfDegree k hk U hdegree hcard).prefixDegree N):ℝ)/
            exactBenchmark (b+(selectionOfDegree k hk U hdegree hcard).prefixDegree N)) :=
  (selectionOfDegree k hk U hdegree hcard).direct_physical_bound hclass hU b P hP

end Physical
end SymmetricSubgroupAsymptotics.BinaryTransitivePowerSevenBoundary

end
