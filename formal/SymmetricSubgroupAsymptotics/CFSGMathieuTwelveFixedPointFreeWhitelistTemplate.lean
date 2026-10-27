import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveFixedPointFreeInvolutionChart
import SymmetricSubgroupAsymptotics.FiniteListBooleanReflection
import Mathlib.Data.Finset.Card

/-! Actual centralizer coverage from the12*10*8 completion-code checks.
Only proved finite Boolean equalities are certificate inputs. The final
concrete module must supply them; no capacity or membership converse is
assumed at a global endpoint. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveFixedPointFreeWhitelistTemplate
open CFSG.Certificates.Mathieu12 CFSGMathieuTwelvePresentationWords
open CFSGMathieuTwelveFixedPointFreeInvolutionChart
open CFSGMathieuTwelveSharpFiveRigidity FinitePermutationCycleSeedAssignments
open FiniteListBooleanReflection

abbrev RawTriple := ℕ × (ℕ × ℕ)
abbrev Selector := ℕ → ℕ → ℕ → ℕ

def coordinates (seed : Fin 3 → Fin 12) : RawTriple :=
  ((seed 0).val,((seed 1).val,(seed 2).val))

theorem coordinates_injective : Function.Injective coordinates := by
  intro s t he
  funext i
  apply Fin.ext
  fin_cases i
  · exact congrArg (fun q : RawTriple => q.1) he
  · exact congrArg (fun q : RawTriple => q.2.1) he
  · exact congrArg (fun q : RawTriple => q.2.2) he

def secondDomain (a : ℕ) : List ℕ :=
  (List.range 12).filter (fun b => decide (b ≠ a ∧ b ≠ rawC a))

def thirdDomain (a b : ℕ) : List ℕ :=
  (List.range 12).filter (fun c => decide (c ≠ a ∧ c ≠ rawC a ∧ c ≠ b ∧ c ≠ rawC b))

private theorem separated_values (seed : Fin 3 → Fin 12)
    (hs : CycleSeparated originalC.val 2 seed) (i j : Fin 3) (hne : i ≠ j) :
    (seed j).val ≠ (seed i).val ∧ (seed j).val ≠ rawC (seed i).val := by
  have h0 : seed i ≠ seed j := by
    simpa only [pow_zero,Equiv.Perm.one_apply] using hs.2.2 i j hne (0 : Fin 2)
  have h1 : originalC.val (seed i) ≠ seed j := by
    simpa only [pow_one] using hs.2.2 i j hne (1 : Fin 2)
  refine ⟨Fin.val_injective.ne (Ne.symm h0),?_⟩
  rw [rawC_eq]
  exact Fin.val_injective.ne (Ne.symm h1)

theorem mem_secondDomain (seed : Fin 3 → Fin 12)
    (hs : CycleSeparated originalC.val 2 seed) :
    (seed 1).val ∈ secondDomain (seed 0).val := by
  have h := separated_values seed hs 0 1 (by decide)
  simpa only [secondDomain,List.mem_filter,List.mem_range,decide_eq_true_eq] using
    And.intro (seed 1).isLt h

theorem mem_thirdDomain (seed : Fin 3 → Fin 12)
    (hs : CycleSeparated originalC.val 2 seed) :
    (seed 2).val ∈ thirdDomain (seed 0).val (seed 1).val := by
  have h0 := separated_values seed hs 0 2 (by decide)
  have h1 := separated_values seed hs 1 2 (by decide)
  simpa only [thirdDomain,List.mem_filter,List.mem_range,decide_eq_true_eq] using
    And.intro (seed 2).isLt ⟨h0.1,h0.2,h1.1,h1.2⟩

def codeCheck (failure : Selector) (whitelist : List RawTriple) (a b c : ℕ) : Bool :=
  whitelist.contains (a,(b,c)) ||
    (let p := failure a b c % 12
     !(rawChart a b c (rawC p) == rawC (rawChart a b c p)))

def batchCheck (failure : Selector) (whitelist : List RawTriple) (a : ℕ) : Bool :=
  (secondDomain a).all (fun b => (thirdDomain a b).all (codeCheck failure whitelist a b))

theorem commuting_raw_point (seed : Fin 3 → Fin 12)
    (hs : CycleSeparated originalC.val 2 seed)
    (hc : Commute (chart seed hs).val originalC.val) (p : Fin 12) :
    rawChart (seed 0).val (seed 1).val (seed 2).val (rawC p.val) =
      rawC (rawChart (seed 0).val (seed 1).val (seed 2).val p.val) := by
  calc
    _ = rawChart (seed 0).val (seed 1).val (seed 2).val (originalC.val p).val := by rw [rawC_eq]
    _ = ((chart seed hs).val (originalC.val p)).val := rawChart_eq seed hs _
    _ = (originalC.val ((chart seed hs).val p)).val :=
      congrArg Fin.val (congrArg (fun z : Perm12 => z p) hc.eq)
    _ = rawC ((chart seed hs).val p).val := (rawC_eq _).symm
    _ = _ := by rw [rawChart_eq]

theorem actual_seed_images_mem (failure : Selector) (whitelist : List RawTriple)
    (checks : ∀ a : Fin 12, batchCheck failure whitelist a.val = true)
    (g : Subgroup.centralizer ({originalC} : Set M12)) :
    coordinates (imageSeeds g) ∈ whitelist := by
  let seed := imageSeeds g
  have hs : CycleSeparated originalC.val 2 seed := imageSeeds_separated g
  have h1 := List.all_eq_true.mp (checks (seed 0)) (seed 1).val (mem_secondDomain seed hs)
  have h2 := List.all_eq_true.mp h1 (seed 2).val (mem_thirdDomain seed hs)
  change (whitelist.contains (coordinates seed) || _) = true at h2
  rw [Bool.or_eq_true_eq_eq_true_or_eq_true] at h2
  rcases h2 with hw | hn
  · exact List.contains_iff_mem.mp hw
  · exfalso
    apply not_beq_sound _ _ hn
    have hc : Commute (chart seed hs).val originalC.val := by
      change Commute (chart (imageSeeds g) (imageSeeds_separated g)).val originalC.val
      rw [chart_eq_centralizer]
      change g.val.val * originalC.val = originalC.val * g.val.val
      simpa only [Subgroup.coe_mul] using congrArg (fun z : M12 => z.val)
        (Subgroup.mem_centralizer_singleton_iff.mp g.property)
    exact commuting_raw_point seed hs hc
      ⟨failure (seed 0).val (seed 1).val (seed 2).val % 12,Nat.mod_lt _ (by decide)⟩

theorem centralizer_card_le_whitelist (failure : Selector) (whitelist : List RawTriple)
    (checks : ∀ a : Fin 12, batchCheck failure whitelist a.val = true) :
    Nat.card (Subgroup.centralizer ({originalC} : Set M12)) ≤ whitelist.toFinset.card := by
  let f : Subgroup.centralizer ({originalC} : Set M12) →
      {q : RawTriple // q ∈ whitelist.toFinset} :=
    fun g => ⟨coordinates (imageSeeds g),List.mem_toFinset.mpr (actual_seed_images_mem failure whitelist checks g)⟩
  have hseed : Function.Injective imageSeeds := by
    apply FiniteBaseCentralizerSeedBounds.seed_evaluation_injective M12Subgroup.subtype originalC
      sourceTuple (fun g h he => eq_of_agree_five sourceTuple g h he) sourceSeeds
    intro t
    exact ⟨(labels t).1,(labels t).2.val,rfl⟩
  have hf : Function.Injective f := by
    intro g h he
    exact hseed (coordinates_injective (congrArg Subtype.val he))
  exact (Nat.card_le_card_of_injective f hf).trans_eq
    (by rw [Nat.card_eq_fintype_card,Fintype.card_coe])

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveFixedPointFreeWhitelistTemplate
