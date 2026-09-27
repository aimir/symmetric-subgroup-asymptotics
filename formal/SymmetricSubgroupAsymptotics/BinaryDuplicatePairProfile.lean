import SymmetricSubgroupAsymptotics.OrbitProfilePairMarks
import SymmetricSubgroupAsymptotics.BinaryDuplicatePairModelCount
import SymmetricSubgroupAsymptotics.RepeatedMarkerMergedProfile
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Physical duplicate-pair incidence with the original one-quarter weight

All exterior original colors and occurrences are fixed and retained. Only
the number of occurrences of the original two-point color changes. The
source counts an unordered pair of actual two-point orbits with equal
characters; the target retains one pointed actual pair. The equality uses
the original normalizer two and the original occurrence factorials.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.BinaryDuplicatePairProfile

open RepeatedMarkerMergedProfile RepeatedCharacterCollapse
open PermutationPairOrbitMarks

variable {α : Type} [Fintype α] (Ω : α → Type)
    [∀ a, Fintype (Ω a)] [∀ a, Nonempty (Ω a)]
    (m : α → ℕ) (U : ∀ a, Subgroup (Equiv.Perm (Ω a)))

local instance finiteSubgroups (G : Type*) [Group G] [Finite G] : Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

abbrev SignFamily (p : ℕ) :=
  RepeatedCharacterFixedAllocation.Family (C := Sign) (Fin p)
    (OrbitProfileProductFull m U)

/-- Use the literal finite ambient set directly, avoiding repeated instance
search through the nested full-coordinate family predicate. -/
local instance signFamilyFinite (p : ℕ) : Finite (SignFamily Ω m U p) :=
  Finite.of_injective
    (fun Y : SignFamily Ω m U p =>
      (Y.val : Set ((Fin p → Sign) × Exterior Ω m U)))
    (fun _ _ h => Subtype.ext (SetLike.coe_injective h))

local instance signFamilyFintype (p : ℕ) : Fintype (SignFamily Ω m U p) :=
  @Fintype.ofFinite (SignFamily Ω m U p) (signFamilyFinite Ω m U p)

abbrev Model (p : ℕ) :=
  {K : Subgroup (Equiv.Perm (ModelPoints Ω m p)) //
    OrbitProfileFull (action Ω U) 1 K}

abbrev Physical (p : ℕ) :=
  AssembledOrbitProfile (OrbitProfileFull (action Ω U) (m := RepeatedMarkerMergedProfile.multiplicity m p) 1)

def originalChart (p : ℕ) := (productEquiv Ω m U p).symm

theorem originalChart_full_iff (p : ℕ)
    (Y : Subgroup ((Fin p → Sign) × Exterior Ω m U)) :
    OrbitProfileProductFull (RepeatedMarkerMergedProfile.multiplicity m p) (action Ω U)
      (Y.map (originalChart Ω m U p).toMonoidHom) ↔
    (∀ j, Function.Surjective (character Y j)) ∧
      OrbitProfileProductFull m U (Y.map (MonoidHom.snd _ _)) := by
  constructor
  · intro h
    constructor
    · intro j z
      obtain ⟨d, hd⟩ := h (.inl PUnit.unit) j (binaryMarkerLocalEquiv z)
      obtain ⟨y, hy, he⟩ := Subgroup.mem_map.mp d.property
      refine ⟨⟨y, hy⟩, ?_⟩
      apply binaryMarkerLocalEquiv.injective
      change binaryMarkerLocalEquiv (y.1 j) = binaryMarkerLocalEquiv z
      exact (congrArg (fun v : Original Ω m U p => v (.inl PUnit.unit) j) he).trans hd
    · intro a j u
      obtain ⟨d, hd⟩ := h (.inr a) j u
      obtain ⟨y, hy, he⟩ := Subgroup.mem_map.mp d.property
      exact ⟨⟨y.2, Subgroup.mem_map.mpr ⟨y, hy, rfl⟩⟩,
        (congrArg (fun v : Original Ω m U p => v (.inr a) j) he).trans hd⟩
  · rintro ⟨hnew, hext⟩ a j u
    cases a with
    | inl a =>
      cases a
      obtain ⟨y, hy⟩ := hnew j (binaryMarkerLocalEquiv.symm u)
      refine ⟨⟨originalChart Ω m U p y.val, Subgroup.mem_map.mpr ⟨y.val, y.property, rfl⟩⟩, ?_⟩
      change binaryMarkerLocalEquiv (y.val.1 j) = u
      change y.val.1 j = binaryMarkerLocalEquiv.symm u at hy
      rw [hy, binaryMarkerLocalEquiv.apply_symm_apply]
    | inr a =>
      obtain ⟨d, hd⟩ := hext a j u
      obtain ⟨y, hy, he⟩ := Subgroup.mem_map.mp d.property
      refine ⟨⟨originalChart Ω m U p y, Subgroup.mem_map.mpr ⟨y, hy, rfl⟩⟩, ?_⟩
      change y.2 a j = u
      exact (congrArg (fun v : Exterior Ω m U => v a j) he).trans hd

/-- The original sign model is transported to the same literal full
permutation model, retaining the full exterior image. -/
def modelEquiv (p : ℕ) : SignFamily Ω m U p ≃ Model Ω m U p :=
  ((originalChart Ω m U p).mapSubgroup.toEquiv.subtypeEquiv
    (fun Y => (originalChart_full_iff Ω m U p Y).symm)).trans
      (orbitProfileProductFullEquiv (RepeatedMarkerMergedProfile.multiplicity m p) (action Ω U))

theorem pair_degree_iff
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2) (a : PUnit.{1} ⊕ α) :
    Nat.card (points Ω a) = 2 ↔ a = .inl PUnit.unit := by
  cases a with
  | inl a => cases a; simp only [Nat.card_eq_fintype_card, point_card_pair, true_iff]
  | inr a =>
      change Nat.card (Ω a) = 2 ↔ Sum.inr a = Sum.inl PUnit.unit
      simp only [Nat.card_eq_fintype_card, hdegree a, false_iff, Sum.inr_ne_inl]

private theorem sign_eq_iff (a b : Sign) : (a = 1 ↔ b = 1) ↔ a = b := by
  have h : ∀ a b : ZMod 2, (a = 0 ↔ b = 0) ↔ a = b := by decide
  constructor
  · intro hab
    apply Multiplicative.toAdd.injective
    apply (h a.toAdd b.toAdd).mp
    change (a = 1 ↔ b = 1)
    exact hab
  · intro hab
    rw [hab]

theorem model_sameAction_iff (p : ℕ) (Y : SignFamily Ω m U p) (j l : Fin p) :
    SameAction (modelEquiv Ω m U p Y).val
      (OrbitProfilePairMarks.block (.inl PUnit.unit) j)
      (OrbitProfilePairMarks.block (.inl PUnit.unit) l) ↔
        character Y.val j = character Y.val l := by
  change SameAction
    ((Y.val.map (originalChart Ω m U p).toMonoidHom).map
      (orbitProfileProductAction (RepeatedMarkerMergedProfile.multiplicity m p) (action Ω U))) _ _ ↔ _
  rw [OrbitProfilePairMarks.sameAction_product_blocks]
  constructor
  · intro h
    apply MonoidHom.ext
    intro y
    apply (sign_eq_iff _ _).mp
    have hy := h (originalChart Ω m U p y.val)
      (Subgroup.mem_map.mpr ⟨y.val, y.property, rfl⟩)
    change (binaryMarkerLocalEquiv (y.val.1 j) = 1 ↔
      binaryMarkerLocalEquiv (y.val.1 l) = 1) at hy
    simpa only [binaryMarkerLocalEquiv.map_eq_one_iff] using hy
  · intro h d hd
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hd
    have he := congrArg (fun χ : Y.val →* Sign => χ ⟨y, hy⟩) h
    change y.1 j = y.1 l at he
    change binaryMarkerLocalEquiv (y.1 j) = 1 ↔ binaryMarkerLocalEquiv (y.1 l) = 1
    rw [he]

def modelDuplicateEquiv (n : ℕ) (Y : SignFamily Ω m U (n+2))
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2) :
    {s : BinaryDuplicatePairModelCount.Selection n //
      BinaryDuplicatePairModelCount.Duplicate s Y.val} ≃
        DuplicateMark (modelEquiv Ω m U (n+2) Y).val := by
  let e : {s : BinaryDuplicatePairModelCount.Selection n //
      BinaryDuplicatePairModelCount.Duplicate s Y.val} ≃
      OrbitProfilePairMarks.OccurrenceMark
        (K := (modelEquiv Ω m U (n+2) Y).val) (.inl PUnit.unit) :=
    { toFun := fun z => ⟨z.val.val, z.val.property, by
        intro j hj l hl
        exact (model_sameAction_iff Ω m U (n+2) Y j l).mpr (z.property j hj l hl)⟩
      invFun := fun z => ⟨⟨z.val, z.property.1⟩, by
        intro j hj l hl
        exact (model_sameAction_iff Ω m U (n+2) Y j l).mp (z.property.2 j hj l hl)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact e.trans (OrbitProfilePairMarks.duplicateMarkEquiv
    (modelEquiv Ω m U (n+2) Y).property (action_transitive Ω U htrans)
    (.inl PUnit.unit) (pair_degree_iff Ω hdegree))

/-- The complete model incidence is derived from reversible collapse of
each actual selected pair; no model-count hypothesis is supplied. -/
theorem model_duplicate_sum (n : ℕ)
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2) :
    (∑ K : Model Ω m U (n+2), Nat.card (DuplicateMark K.val)) =
      (n+2).choose 2 * Nat.card (Model Ω m U (n+1)) := by
  calc
    _ = ∑ Y : SignFamily Ω m U (n+2),
        Nat.card (DuplicateMark (modelEquiv Ω m U (n+2) Y).val) :=
      (Fintype.sum_equiv (modelEquiv Ω m U (n+2)) _ _ (fun _ => rfl)).symm
    _ = ∑ Y : SignFamily Ω m U (n+2),
        Nat.card {s : BinaryDuplicatePairModelCount.Selection n //
          BinaryDuplicatePairModelCount.Duplicate s Y.val} := by
      apply Finset.sum_congr rfl
      intro Y _
      exact (Nat.card_congr (modelDuplicateEquiv Ω m U n Y htrans hdegree)).symm
    _ = (n+2).choose 2 * Nat.card (SignFamily Ω m U (n+1)) := by
      rw [← Nat.card_sigma]
      exact BinaryDuplicatePairModelCount.incidence_card
        (C := Sign) (D := Exterior Ω m U) n (OrbitProfileProductFull m U)
    _ = _ := by rw [Nat.card_congr (modelEquiv Ω m U (n+1))]

theorem physical_card (p : ℕ)
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2) :
    (Nat.card (Physical Ω m U p) : ℚ) =
      ((2*p + exteriorDegree Ω m).factorial : ℚ) * Nat.card (Model Ω m U p) /
        ((2 : ℚ)^p * p.factorial * exteriorDenominator Ω m U) := by
  have h := assembledOrbitProfile_card_rat (fun _ h => h)
    (orbitProfileFull_family_natural (RepeatedMarkerMergedProfile.multiplicity m p) (action Ω U))
    (action_transitive Ω U htrans) (action_separated Ω U hsep hdegree)
  rw [degree Ω m, denominator Ω m U] at h
  exact h

theorem physical_duplicate_sum (n : ℕ)
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2) :
    (∑ H : Physical Ω m U (n+2), (Nat.card (DuplicateMark H.val) : ℚ)) =
      ((2*(n+2) + exteriorDegree Ω m).factorial : ℚ) *
        ((n+2).choose 2 * Nat.card (Model Ω m U (n+1))) /
        ((2 : ℚ)^(n+2) * (n+2).factorial * exteriorDenominator Ω m U) := by
  have h := assembledOrbitProfile_weighted_sum_rat (fun _ h => h)
    (orbitProfileFull_family_natural (RepeatedMarkerMergedProfile.multiplicity m (n+2)) (action Ω U))
    (action_transitive Ω U htrans) (action_separated Ω U hsep hdegree)
    (fun K => Nat.card (DuplicateMark K)) duplicateMark_card_relabel
  have hm : (∑ K : Model Ω m U (n+2), (Nat.card (DuplicateMark K.val) : ℚ)) =
      (n+2).choose 2 * Nat.card (Model Ω m U (n+1)) := by
    exact_mod_cast model_duplicate_sum Ω m U n htrans hdegree
  rw [degree Ω m, denominator Ω m U, hm] at h
  exact h

theorem physical_pair_card (p : ℕ) (H : Physical Ω m U p)
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2) :
    Nat.card (PairOrbit H.val) = p := by
  obtain ⟨⟨g, K⟩, hH⟩ := H.property
  change relabelSubgroup g K.val = H.val at hH
  rw [← hH, ← Nat.card_congr (PermutationPairOrbitMarks.pairOrbitEquiv g K.val)]
  exact OrbitProfilePairMarks.pairOrbit_card K.property (action_transitive Ω U htrans)
    (.inl PUnit.unit) (pair_degree_iff Ω hdegree)

theorem physical_pointed_sum (p : ℕ)
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2) :
    (∑ H : Physical Ω m U p, (Nat.card (PairOrbit H.val) : ℚ)) =
      (p : ℚ) * Nat.card (Physical Ω m U p) := by
  simp_rw [physical_pair_card Ω m U p _ htrans hdegree]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  ring

private theorem quarter_weight (n : ℕ) (E A : ℚ) :
    (((n+2).choose 2 : ℚ) * A) / ((2 : ℚ)^(n+2) * (n+2).factorial * E) =
      ((n+1 : ℕ) : ℚ) / 4 * (A / ((2 : ℚ)^(n+1) * (n+1).factorial * E)) := by
  by_cases hE : E = 0
  · simp [hE]
  have hf (k : ℕ) : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hchoose : ((n+2).choose 2 : ℚ) * 2 * (n.factorial : ℚ) = (n+2).factorial := by
    have hc : (n+2).choose 2 * 2 * n.factorial = (n+2).factorial := by
      simpa using (Nat.choose_mul_factorial_mul_factorial
        (n := n+2) (k := 2) (by omega))
    exact_mod_cast hc
  have hn : (n+1 : ℚ) ≠ 0 := by positivity
  have hn2 : (n+2 : ℚ) ≠ 0 := by positivity
  have hfac1 : ((n+1).factorial : ℚ) = (n+1) * (n.factorial : ℚ) := by
    rw [Nat.factorial_succ]
    push_cast
    rfl
  have hfac2 : ((n+2).factorial : ℚ) = (n+2) * (n+1) * (n.factorial : ℚ) := by
    rw [show n+2 = (n+1)+1 by omega, Nat.factorial_succ]
    push_cast
    rw [hfac1]
    ring
  have hc : ((n+2).choose 2 : ℚ) = (n+2) * (n+1) / 2 := by
    rw [hfac2] at hchoose
    have hc' := mul_right_cancel₀ (hf n) hchoose
    linarith
  have hp : (2 : ℚ)^(n+2) = (2 : ℚ)^(n+1) * 2 := pow_succ _ _
  rw [hc, hp, hfac2, hfac1]
  push_cast
  field_simp [hf, hn, hn2, hE, pow_ne_zero _ (by norm_num : (2 : ℚ) ≠ 0)] <;> ring

/-- Exact physical one-quarter incidence. The target pair is pointed in
all n+1 possible ways. The exterior profile, including any noncritical
original orbit, is literally unchanged. This is not the separate
independent-four-pair moment estimate. -/
theorem normalized_duplicate_incidence (n : ℕ)
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2) :
    (∑ H : Physical Ω m U (n+2), (Nat.card (DuplicateMark H.val) : ℚ)) /
        (2*(n+2) + exteriorDegree Ω m).factorial =
      (1 / 4 : ℚ) * ((n+1 : ℕ) : ℚ) *
        ((Nat.card (Physical Ω m U (n+1)) : ℚ) /
          (2*(n+1) + exteriorDegree Ω m).factorial) := by
  rw [physical_duplicate_sum Ω m U n htrans hsep hdegree,
    physical_card Ω m U (n+1) htrans hsep hdegree]
  have hf (k : ℕ) : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have cancel (F A D : ℚ) (hF : F ≠ 0) : F * A / D / F = A / D := by
    calc
      _ = (F / F) * (A / D) := by ring
      _ = _ := by rw [div_self hF, one_mul]
  rw [cancel _ _ _ (hf _), cancel _ _ _ (hf _), quarter_weight]
  ring

/-- Both sides are sums over actual original subgroups with actual finite
orbit marks. Only the original point-set factorials are normalized away. -/
theorem normalized_duplicate_pointed_incidence (n : ℕ)
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2) :
    (∑ H : Physical Ω m U (n+2), (Nat.card (DuplicateMark H.val) : ℚ)) /
        (2*(n+2) + exteriorDegree Ω m).factorial =
      (1 / 4 : ℚ) *
        ((∑ H : Physical Ω m U (n+1), (Nat.card (PairOrbit H.val) : ℚ)) /
          (2*(n+1) + exteriorDegree Ω m).factorial) := by
  rw [normalized_duplicate_incidence Ω m U n htrans hsep hdegree,
    physical_pointed_sum Ω m U (n+1) htrans hdegree]
  ring

end SymmetricSubgroupAsymptotics.BinaryDuplicatePairProfile
