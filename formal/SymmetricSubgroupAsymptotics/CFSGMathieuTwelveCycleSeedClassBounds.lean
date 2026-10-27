import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveSharpFiveRigidity
import SymmetricSubgroupAsymptotics.FinitePermutationCycleSeedAssignments
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelvePresentationWords
import Mathlib.Data.Fin.VecNotation
import SymmetricSubgroupAsymptotics.SignedPermutationWordPointEvaluation

/-! The original M12 centralizer bounded by a finite set of cycle-seed images.
The first concrete pilot is originalB, two literal four-cycles. Only finite
twelve-point period/coverage facts and144 point assignments are checked. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveCycleSeedClassBounds
open CFSG.Certificates.Mathieu12 CFSGMathieuTwelvePresentationWords
open CFSGMathieuTwelveSharpFiveRigidity FinitePermutationCycleSeedAssignments

theorem original_centralizer_card_le_assignments {r : ℕ} (a : M12)
    (base : Fin 5 ↪ Fin 12) (d : ℕ) (seed : Fin r → Fin 12)
    (covered : ∀ t, ∃ i : Fin r, ∃ n : ℕ, base t = (a.val^n) (seed i))
    (hseed : CycleSeparated a.val d seed) :
    Nat.card (Subgroup.centralizer ({a} : Set M12)) ≤ (assignments a.val d r).card :=
  centralizer_card_le_assignments M12Subgroup.subtype a base
    (fun g h he => eq_of_agree_five base g h he) d seed covered hseed

private def fourBase : Fin 5 ↪ Fin 12 where
  toFun := ![2,6,10,7,3]
  inj' := by decide +kernel

private def fourSeeds : Fin 2 → Fin 12 := ![2,3]

private theorem four_covered (t : Fin 5) :
    ∃ i : Fin 2, ∃ n : ℕ, fourBase t = (originalB.val^n) (fourSeeds i) := by
  fin_cases t
  · exact ⟨0,0,by decide +kernel⟩
  · exact ⟨0,1,by decide +kernel⟩
  · exact ⟨0,2,by decide +kernel⟩
  · exact ⟨0,3,by decide +kernel⟩
  · exact ⟨1,0,by decide +kernel⟩

private theorem four_separated : CycleSeparated originalB.val 4 fourSeeds := by
  decide +kernel

private theorem four_assignment_card : (assignments originalB.val 4 2).card = 32 := by
  decide +kernel

theorem originalB_centralizer_card_le_thirtyTwo :
    Nat.card (Subgroup.centralizer ({originalB} : Set M12)) ≤ 32 :=
  (original_centralizer_card_le_assignments originalB fourBase 4 fourSeeds
    four_covered four_separated).trans_eq four_assignment_card


/- The following nine fixed word literals are certificate inputs transcribed
from the cached source text. Their periods, profile and bounds are proved
below on the actual original pair; no standard-pair recognition is assumed. -/
private def parsedWord (w : String) : List SignedPermutationWordPointEvaluation.Letter :=
  w.toList.map (fun c => if c = 'a' then .first else .second)

private def wordElement (w : String) : M12 :=
  SignedPermutationWordPointEvaluation.eval x y (parsedWord w)

private def wordPermutation (w : String) : Perm12 :=
  SignedPermutationWordPointEvaluation.eval xPermutation yPermutation (parsedWord w)

private theorem map_eval {G H : Type*} [Group G] [Group H] (f : G →* H)
    (a b : G) (w : List SignedPermutationWordPointEvaluation.Letter) :
    f (SignedPermutationWordPointEvaluation.eval a b w) =
      SignedPermutationWordPointEvaluation.eval (f a) (f b) w := by
  induction w with
  | nil => simp only [SignedPermutationWordPointEvaluation.eval,map_one]
  | cons l w ih =>
    cases l <;> simp only [SignedPermutationWordPointEvaluation.eval,
      SignedPermutationWordPointEvaluation.value,map_mul,map_inv,ih]

private theorem word_coe (w : String) : (wordElement w).val = wordPermutation w := by
  have h := map_eval M12Subgroup.subtype x y (parsedWord w)
  change (wordElement w).val =
    SignedPermutationWordPointEvaluation.eval x.val y.val (parsedWord w) at h
  rw [x_coe_eq,y_coe_eq] at h
  exact h

private def orbitBase (pi : Perm12) (d r : ℕ) (hr : 0 < r)
    (seed : Fin r → Fin 12) (t : Fin 5) : Fin 12 :=
  (pi^(t.val%d)) (seed ⟨(t.val/d)%r,Nat.mod_lt _ hr⟩)

private def CycleCertificate (pi : Perm12) (d r : ℕ) (hr : 0 < r) : Prop :=
  ∃ seed : Fin r → Fin 12,
    CycleSeparated pi d seed ∧ Function.Injective (orbitBase pi d r hr seed)

private instance (pi : Perm12) (d r : ℕ) (hr : 0 < r) :
    Decidable (CycleCertificate pi d r hr) := by
  unfold CycleCertificate
  infer_instance

private theorem original_le_of_certificate (a : M12) (d r : ℕ) (hr : 0 < r)
    (hc : CycleCertificate a.val d r hr) :
    Nat.card (Subgroup.centralizer ({a} : Set M12)) ≤ (assignments a.val d r).card := by
  obtain ⟨seed,hseed,hinj⟩ := hc
  let base : Fin 5 ↪ Fin 12 := ⟨orbitBase a.val d r hr seed,hinj⟩
  apply original_centralizer_card_le_assignments a base d seed
  · intro t
    exact ⟨⟨(t.val/d)%r,Nat.mod_lt _ hr⟩,t.val%d,rfl⟩
  · exact hseed

private theorem word_bound (w : String) (d r : ℕ) (hr : 0 < r) (b : ℕ)
    (hc : CycleCertificate (wordPermutation w) d r hr)
    (hb : (assignments (wordPermutation w) d r).card = b) :
    Nat.card (Subgroup.centralizer ({wordElement w} : Set M12)) ≤ b := by
  have hactual : CycleCertificate (wordElement w).val d r hr := by
    rw [word_coe]
    exact hc
  have h := original_le_of_certificate (wordElement w) d r hr hactual
  rw [word_coe] at h
  exact h.trans_eq hb

private theorem row_certificate_0 :
    CycleCertificate (wordPermutation "ababbababb") 3 2 (by decide) := by
  decide +kernel

private theorem row_assignments_0 :
    (assignments (wordPermutation "ababbababb") 3 2).card = 54 := by
  decide +kernel

private theorem row_profile_0 :
    (wordPermutation "ababbababb").cycleType =
      (([3, 3, 3] : List ℕ) : Multiset ℕ) := by
  decide +kernel

private theorem row_certificate_1 :
    CycleCertificate (wordPermutation "ababababbababbabbababababbababbabb") 4 2 (by decide) := by
  decide +kernel

private theorem row_assignments_1 :
    (assignments (wordPermutation "ababababbababbabbababababbababbabb") 4 2).card = 32 := by
  decide +kernel

private theorem row_profile_1 :
    (wordPermutation "ababababbababbabbababababbababbabb").cycleType =
      (([4, 4, 2, 2] : List ℕ) : Multiset ℕ) := by
  decide +kernel

private theorem row_certificate_2 :
    CycleCertificate (wordPermutation "ababababbabbababbababababbabbababb") 4 2 (by decide) := by
  decide +kernel

private theorem row_assignments_2 :
    (assignments (wordPermutation "ababababbabbababbababababbabbababb") 4 2).card = 32 := by
  decide +kernel

private theorem row_profile_2 :
    (wordPermutation "ababababbabbababbababababbabbababb").cycleType =
      (([4, 4] : List ℕ) : Multiset ℕ) := by
  decide +kernel

private theorem row_certificate_3 :
    CycleCertificate (wordPermutation "ababababbabbababababbabb") 5 1 (by decide) := by
  decide +kernel

private theorem row_assignments_3 :
    (assignments (wordPermutation "ababababbabbababababbabb") 5 1).card = 10 := by
  decide +kernel

private theorem row_profile_3 :
    (wordPermutation "ababababbabbababababbabb").cycleType =
      (([5, 5] : List ℕ) : Multiset ℕ) := by
  decide +kernel

private theorem row_certificate_4 :
    CycleCertificate (wordPermutation "abababb") 6 1 (by decide) := by
  decide +kernel

private theorem row_assignments_4 :
    (assignments (wordPermutation "abababb") 6 1).card = 12 := by
  decide +kernel

private theorem row_profile_4 :
    (wordPermutation "abababb").cycleType =
      (([6, 6] : List ℕ) : Multiset ℕ) := by
  decide +kernel

private theorem row_certificate_5 :
    CycleCertificate (wordPermutation "ababb") 6 1 (by decide) := by
  decide +kernel

private theorem row_assignments_5 :
    (assignments (wordPermutation "ababb") 6 1).card = 6 := by
  decide +kernel

private theorem row_profile_5 :
    (wordPermutation "ababb").cycleType =
      (([6, 3, 2] : List ℕ) : Multiset ℕ) := by
  decide +kernel

private theorem row_certificate_6 :
    CycleCertificate (wordPermutation "ababababbababbabb") 8 1 (by decide) := by
  decide +kernel

private theorem row_assignments_6 :
    (assignments (wordPermutation "ababababbababbabb") 8 1).card = 8 := by
  decide +kernel

private theorem row_profile_6 :
    (wordPermutation "ababababbababbabb").cycleType =
      (([8, 4] : List ℕ) : Multiset ℕ) := by
  decide +kernel

private theorem row_certificate_7 :
    CycleCertificate (wordPermutation "ababababbabbababb") 8 1 (by decide) := by
  decide +kernel

private theorem row_assignments_7 :
    (assignments (wordPermutation "ababababbabbababb") 8 1).card = 8 := by
  decide +kernel

private theorem row_profile_7 :
    (wordPermutation "ababababbabbababb").cycleType =
      (([8, 2] : List ℕ) : Multiset ℕ) := by
  decide +kernel

private theorem row_certificate_8 :
    CycleCertificate (wordPermutation "ababababbabb") 10 1 (by decide) := by
  decide +kernel

private theorem row_assignments_8 :
    (assignments (wordPermutation "ababababbabb") 10 1).card = 10 := by
  decide +kernel

private theorem row_profile_8 :
    (wordPermutation "ababababbabb").cycleType =
      (([10, 2] : List ℕ) : Multiset ℕ) := by
  decide +kernel

private def cycleWord (i : Fin 9) : String :=
  match i.val with
  | 0 => "ababbababb"
  | 1 => "ababababbababbabbababababbababbabb"
  | 2 => "ababababbabbababbababababbabbababb"
  | 3 => "ababababbabbababababbabb"
  | 4 => "abababb"
  | 5 => "ababb"
  | 6 => "ababababbababbabb"
  | 7 => "ababababbabbababb"
  | _ => "ababababbabb"

def cycleRepresentative (i : Fin 9) : M12 := wordElement (cycleWord i)

def cycleCeiling (i : Fin 9) : ℕ := ![54,32,32,10,12,6,8,8,10] i

def cycleProfile (i : Fin 9) : Multiset ℕ :=
  match i.val with
  | 0 => (([3, 3, 3] : List ℕ) : Multiset ℕ)
  | 1 => (([4, 4, 2, 2] : List ℕ) : Multiset ℕ)
  | 2 => (([4, 4] : List ℕ) : Multiset ℕ)
  | 3 => (([5, 5] : List ℕ) : Multiset ℕ)
  | 4 => (([6, 6] : List ℕ) : Multiset ℕ)
  | 5 => (([6, 3, 2] : List ℕ) : Multiset ℕ)
  | 6 => (([8, 4] : List ℕ) : Multiset ℕ)
  | 7 => (([8, 2] : List ℕ) : Multiset ℕ)
  | _ => (([10, 2] : List ℕ) : Multiset ℕ)

theorem nine_centralizer_bounds (i : Fin 9) :
    Nat.card (Subgroup.centralizer ({cycleRepresentative i} : Set M12)) ≤ cycleCeiling i := by
  fin_cases i
  · exact word_bound "ababbababb" 3 2 (by decide) 54 row_certificate_0 row_assignments_0
  · exact word_bound "ababababbababbabbababababbababbabb" 4 2 (by decide) 32 row_certificate_1 row_assignments_1
  · exact word_bound "ababababbabbababbababababbabbababb" 4 2 (by decide) 32 row_certificate_2 row_assignments_2
  · exact word_bound "ababababbabbababababbabb" 5 1 (by decide) 10 row_certificate_3 row_assignments_3
  · exact word_bound "abababb" 6 1 (by decide) 12 row_certificate_4 row_assignments_4
  · exact word_bound "ababb" 6 1 (by decide) 6 row_certificate_5 row_assignments_5
  · exact word_bound "ababababbababbabb" 8 1 (by decide) 8 row_certificate_6 row_assignments_6
  · exact word_bound "ababababbabbababb" 8 1 (by decide) 8 row_certificate_7 row_assignments_7
  · exact word_bound "ababababbabb" 10 1 (by decide) 10 row_certificate_8 row_assignments_8

theorem cycleRepresentative_cycleType (i : Fin 9) :
    (cycleRepresentative i).val.cycleType = cycleProfile i := by
  change (wordElement (cycleWord i)).val.cycleType = _
  rw [word_coe]
  fin_cases i
  · exact row_profile_0
  · exact row_profile_1
  · exact row_profile_2
  · exact row_profile_3
  · exact row_profile_4
  · exact row_profile_5
  · exact row_profile_6
  · exact row_profile_7
  · exact row_profile_8

private theorem cycleProfile_injective : Function.Injective cycleProfile := by
  decide +kernel

theorem nine_representatives_separated (i j : Fin 9)
    (h : IsConj (cycleRepresentative i) (cycleRepresentative j)) : i = j := by
  obtain ⟨g,hg⟩ := isConj_iff.mp h
  have hp : IsConj (cycleRepresentative i).val (cycleRepresentative j).val := by
    apply isConj_iff.mpr
    exact ⟨g.val,congrArg (fun z : M12 => z.val) hg⟩
  have ht := Equiv.Perm.isConj_iff_cycleType_eq.mp hp
  rw [cycleRepresentative_cycleType,cycleRepresentative_cycleType] at ht
  exact cycleProfile_injective ht

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveCycleSeedClassBounds
