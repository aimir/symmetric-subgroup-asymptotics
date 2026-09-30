import SymmetricSubgroupAsymptotics.BinaryDegree16DirectOwnerRouting

/-!
# Normalizer-saturated direct ownership in degree sixteen

A degree-sixteen direct owner supplies an original-weight entry on one
literal normal axis.  Physical pointing, however, acts on that axis by the
normalizer of the original action.  This file closes that mismatch without
marking a normalizer element: existence of a direct entry is transported
through every action automorphism, hence is a normalizer-natural predicate.

The resulting option-valued selection uses the transported entry on every
accepted axis and zero data elsewhere.  The latter axes have empty surviving
fibres because the physical predicate itself requires an entry.  Thus the
unmarked degree-sixteen direct family enters one finite, forward,
exponentially contractive original-weight row.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryDegree16NormalizerSaturatedDirect

open SymmetricSubgroupAsymptotics
open BinaryDegree16SplitAnalyticClosure
open BinaryDegree16PhysicalAnalyticClosure
open BinaryDegree16DirectOwnerRouting

/-- A rejected finite Goursat fibre has zero surviving epimorphisms.  This
small local form avoids importing the unrelated nonbinary owner assembly. -/
private theorem survivingEpiCount_eq_zero_of_rejected
    {w b : ℕ} (U : Subgroup (Equiv.Perm (Fin w)))
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (A : {N : Subgroup U // N.Normal})
    (J : Subgroup (Equiv.Perm (Fin b)))
    (hreject : ∀ beta : GroupEpimorphism J (U ⧸ A.1),
      ¬ P (fusionFullGoursatEncode A J beta).1) :
    fusionSurvivingEpiCount U P A J = 0 := by
  unfold fusionSurvivingEpiCount
  letI : IsEmpty {beta : GroupEpimorphism J (U ⧸ A.1) //
      P (fusionFullGoursatEncode A J beta).1} :=
    ⟨fun beta => hreject beta.1 beta.2⟩
  simp

section EntryTransport

variable {h : ℕ}
variable {U V : Subgroup (Equiv.Perm (Fin (2*h)))}
variable {N : Subgroup U} [N.Normal]
variable {M : Subgroup V} [M.Normal]

/-- Transport a direct entry through an arbitrary equivalence of the two
literal action groups.  The numerical data and moment function are retained.
For survival, forgetting the predicate and transporting the complete finite
epimorphism set gives the required envelope on the new action. -/
def transportWeightedEntry (e : U ≃* V)
    (hM : N.map e.toMonoidHom = M)
    (E : BinaryOriginalWeightedDirectEntry U N) :
    BinaryOriginalWeightedDirectEntry V M where
  prefixDegree := E.prefixDegree
  markerHalf := E.markerHalf
  liftConstant := E.liftConstant
  gapParameter := E.gapParameter
  momentWeight := fun {b} J => E.momentWeight J
  prefix_eq_two_mul := E.prefix_eq_two_mul
  prefix_lt := E.prefix_lt
  liftConstant_nonneg := E.liftConstant_nonneg
  gapParameter_pos := E.gapParameter_pos
  moment_le := E.moment_le
  original_envelope := by
    intro b P J
    let q : (U ⧸ N) ≃* (V ⧸ M) := QuotientGroup.congr N M e hM
    have hsubNat :
        Nat.card {beta : GroupEpimorphism J (V ⧸ M) //
          P (fusionFullGoursatEncode ⟨M,inferInstance⟩ J beta).1} ≤
          Nat.card (GroupEpimorphism J (V ⧸ M)) :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    have hquot :
        Nat.card (GroupEpimorphism J (U ⧸ N)) =
          Nat.card (GroupEpimorphism J (V ⧸ M)) :=
      fusionGroupEpimorphism_card_congr (MulEquiv.refl J) q
    calc
      fusionSurvivingEpiCount V P ⟨M,inferInstance⟩ J ≤
          (Nat.card (GroupEpimorphism J (V ⧸ M)) : ℝ) := by
        unfold fusionSurvivingEpiCount
        exact_mod_cast hsubNat
      _ = (Nat.card (GroupEpimorphism J (U ⧸ N)) : ℝ) := by
        exact_mod_cast hquot.symm
      _ ≤ fusionLocalFactor b h E.prefixDegree E.liftConstant E.gapParameter *
          E.momentWeight J := by
        let allEquiv : {beta : GroupEpimorphism J (U ⧸ N) // True} ≃
            GroupEpimorphism J (U ⧸ N) :=
          { toFun := Subtype.val
            invFun := fun beta => ⟨beta,trivial⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
        have hcard := Nat.card_congr allEquiv
        have htarget := E.original_envelope (fun _ => True) J
        unfold fusionSurvivingEpiCount at htarget
        change (Nat.card {beta : GroupEpimorphism J (U ⧸ N) // True} : ℝ) ≤ _
          at htarget
        rw [hcard] at htarget
        exact htarget

/-- Existence of an original-weight entry on a raw subgroup.  The normality
proof is retained existentially so this predicate is meaningful before a
full-projection proof has installed a typeclass instance. -/
def HasWeightedEntryAxis (U : Subgroup (Equiv.Perm (Fin (2*h))))
    (N : Subgroup U) : Prop :=
  ∃ hN : N.Normal,
    Nonempty (@BinaryOriginalWeightedDirectEntry h U N hN)

/-- Entry existence is stable under every action equivalence, and hence in
particular under the action normalizer used by physical pointing. -/
theorem hasWeightedEntryAxis_map (e : U ≃* V)
    {N : Subgroup U} (H : HasWeightedEntryAxis U N) :
    HasWeightedEntryAxis V (N.map e.toMonoidHom) := by
  obtain ⟨hN,⟨E⟩⟩ := H
  let hM : (N.map e.toMonoidHom).Normal :=
    Subgroup.Normal.map hN e.toMonoidHom e.surjective
  refine ⟨hM,?_⟩
  letI : N.Normal := hN
  letI : (N.map e.toMonoidHom).Normal := hM
  exact ⟨transportWeightedEntry e rfl E⟩

/-- On a packaged normal axis, existential normality can be replaced by the
literal packaged instance without changing the entry type. -/
theorem nonemptyEntry_of_hasWeightedEntryAxis
    (A : {N : Subgroup U // N.Normal})
    (H : HasWeightedEntryAxis U A.1) :
    Nonempty (BinaryOriginalWeightedDirectEntry U A.1) := by
  obtain ⟨hN,hE⟩ := H
  letI : A.1.Normal := hN
  simpa only using hE

end EntryTransport

section PartialSelection

variable {h : ℕ}
variable {U : Subgroup (Equiv.Perm (Fin (2*h)))}

/-- An entry is selected exactly on the accepted normal axes. -/
abbrev PartialSelection :=
  ∀ A : {N : Subgroup U // N.Normal},
    Option (BinaryOriginalWeightedDirectEntry U A.1)

namespace PartialSelection

variable (C : PartialSelection (h := h) (U := U))

def prefixDegree (A : {N : Subgroup U // N.Normal}) : ℕ :=
  match C A with
  | some E => E.prefixDegree
  | none => 0

def markerHalf (A : {N : Subgroup U // N.Normal}) : ℕ :=
  match C A with
  | some E => E.markerHalf
  | none => 0

def liftConstant (A : {N : Subgroup U // N.Normal}) : ℝ :=
  match C A with
  | some E => E.liftConstant
  | none => 0

def gapParameter (A : {N : Subgroup U // N.Normal}) : ℝ :=
  match C A with
  | some E => E.gapParameter
  | none => 1

def momentWeight (A : {N : Subgroup U // N.Normal}) {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) : ℝ :=
  match C A with
  | some E => E.momentWeight J
  | none => 0

theorem prefix_eq_two_mul (A : {N : Subgroup U // N.Normal}) :
    C.prefixDegree A = 2*C.markerHalf A := by
  cases hC : C A with
  | none => simp [prefixDegree,markerHalf,hC]
  | some E => simpa [prefixDegree,markerHalf,hC] using E.prefix_eq_two_mul

theorem prefix_lt (hh : 0 < h) (A : {N : Subgroup U // N.Normal}) :
    C.prefixDegree A < 2*h := by
  cases hC : C A with
  | none => simp [prefixDegree,hC]; omega
  | some E => simpa [prefixDegree,hC] using E.prefix_lt

theorem liftConstant_nonneg (A : {N : Subgroup U // N.Normal}) :
    0 ≤ C.liftConstant A := by
  cases hC : C A with
  | none => simp [liftConstant,hC]
  | some E => simpa [liftConstant,hC] using E.liftConstant_nonneg

theorem gapParameter_pos (A : {N : Subgroup U // N.Normal}) :
    0 < C.gapParameter A := by
  cases hC : C A with
  | none => simp [gapParameter,hC]
  | some E => simpa [gapParameter,hC] using E.gapParameter_pos

theorem firstMoment_le (A : {N : Subgroup U // N.Normal}) (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)), C.momentWeight A J) ≤
      (subgroupCount (b+C.prefixDegree A) : ℝ) := by
  cases hC : C A with
  | none =>
      simp [momentWeight,prefixDegree,hC]
  | some E =>
      simpa only [momentWeight,prefixDegree,hC,pow_one,one_mul] using
        E.moment_le b 1

/-- Absent entries may be filled by zero numerical data exactly when their
surviving epimorphism fibres are empty. -/
theorem original_envelope {b : ℕ}
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (hexcluded : ∀ A, C A = none → ∀ J,
      fusionSurvivingEpiCount U P A J = 0)
    (A : {N : Subgroup U // N.Normal})
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount U P A J ≤
      fusionLocalFactor b h (C.prefixDegree A) (C.liftConstant A)
        (C.gapParameter A) * C.momentWeight A J := by
  cases hC : C A with
  | none => simp [prefixDegree,liftConstant,gapParameter,momentWeight,hC,
      hexcluded A hC J]
  | some E =>
      simpa only [prefixDegree,liftConstant,gapParameter,momentWeight,hC] using
        E.original_envelope P J

end PartialSelection
end PartialSelection

section DegreeSixteen

/-- All literal transitive binary actions on sixteen points.  No catalogue
representative or order cutoff is inserted into the counting index. -/
abbrev Action :=
  {U : Subgroup (Equiv.Perm (Fin 16)) //
    IsPGroup 2 U ∧ MulAction.IsPretransitive U (Fin 16)}

instance actionFintype : Fintype Action := Fintype.ofFinite _

def action (i : Action) : Subgroup (Equiv.Perm (Fin 16)) := i.1

theorem action_binary (i : Action) : IsPGroup 2 (action i) := i.2.1

theorem action_transitive (i : Action) :
    MulAction.IsPretransitive (action i) (Fin 16) := i.2.2

/-- The local accepted predicate is the automorphism-saturated existence of
an original-weight entry on the literal Goursat axis. -/
def localPredicate {b : ℕ} (i : Action)
    (K : Subgroup (action i × Equiv.Perm (Fin b))) : Prop :=
  HasWeightedEntryAxis (h := 8) (action i) K.goursatFst

theorem localPredicate_natural {b : ℕ} (i : Action) :
    FusionOrbitNatural (action i) (localPredicate (b := b) i) := by
  apply fusionOrbitNatural_axis
  intro c N hN
  exact hasWeightedEntryAxis_map ((action i).normalizerMonoidHom c) hN

/-- Choose one entry on every accepted literal normal and choose none on all
other normals.  The choice is made before the exterior degree and source. -/
def selection (i : Action) : PartialSelection (h := 8) (U := action i) :=
  fun A => if hA : Nonempty (BinaryOriginalWeightedDirectEntry (h := 8)
      (action i) A.1) then some (Classical.choice hA) else none

theorem selection_eq_none_iff (i : Action)
    (A : {N : Subgroup (action i) // N.Normal}) :
    selection i A = none ↔
      ¬ Nonempty (BinaryOriginalWeightedDirectEntry (h := 8) (action i) A.1) := by
  simp [selection]

/-- A zero option is a genuinely empty local fibre for the saturated
physical predicate. -/
theorem selection_excluded {b : ℕ} (i : Action)
    (A : {N : Subgroup (action i) // N.Normal})
    (hA : selection i A = none)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount (action i) (localPredicate i) A J = 0 := by
  apply survivingEpiCount_eq_zero_of_rejected (action i) (localPredicate i) A J
  intro beta hbeta
  have haxis : HasWeightedEntryAxis (h := 8) (action i) A.1 := by
    simpa only [localPredicate,fusionFullGoursatEncode,
      fusionQuotientGraph_axis,QuotientGroup.ker_mk'] using hbeta
  have hentry := @nonemptyEntry_of_hasWeightedEntryAxis 8 (action i) A haxis
  exact (selection_eq_none_iff i A).mp hA hentry

/-- The complete original-action row for the normalizer-saturated direct
sector.  Every normal remains in the sum; absent axes contribute zero. -/
def directRow (n m : ℕ) : ℝ :=
  fusionPhysicalDirectRow (fun _ : Action => 8) action
    (fun i A => (selection i).prefixDegree A)
    (fun i A => (selection i).liftConstant A)
    (fun i A => (selection i).gapParameter A) n m

/-- A direct physical witness enters the saturated canonical family on its
actual restriction image.  The orbit and its chart remain existential and
do not become counted markings. -/
theorem directFamily_cover {n : ℕ} (hn : 16 ≤ n)
    (H : Subgroup (Equiv.Perm (Fin n)))
    (hH : H ∈ directFamily n) :
    ∃ i : Action,
      H ∈ FusionCanonicalFamily (h := 8) (action i) hn (localPredicate i) := by
  obtain ⟨W,howner⟩ := hH
  let i : Action := ⟨W.action,W.action_binary,inferInstance⟩
  refine ⟨i,?_⟩
  apply fusionCanonicalFamily_of_chart (h := 8) (action i) hn H W.chart
    W.pulled_preserves W.first_projection (localPredicate i)
  change HasWeightedEntryAxis (h := 8) W.action W.axis
  exact ⟨W.axis_normal,
    BinaryDegree16DirectOwnerRouting.DirectOwner.weightedEntry
      W.action_binary howner⟩

/-- The unmarked direct family has a strict forward original-weight
recurrence.  No action catalogue, marked orbit, coarse subgroup bound, or
external normal-axis selection remains. -/
theorem direct_recurrence (n : ℕ) (hn : 16 ≤ n) :
    (Nat.card (directFamily n) : ℝ)/exactBenchmark n ≤
      ∑ m ∈ Finset.range n, directRow n m *
        ((subgroupCount m : ℝ)/exactBenchmark m) := by
  unfold directRow
  apply fusionPhysicalUnion_direct_recurrence
    (fun _ : Action => 8) action n (fun _ => hn) (directFamily n)
    (fun i => localPredicate i) (fun i => localPredicate_natural i)
    (directFamily_cover hn)
    (fun i A => (selection i).prefixDegree A)
    (fun i A => (selection i).liftConstant A)
    (fun i A => (selection i).gapParameter A)
    (fun i A J => (selection i).momentWeight A J)
  · intro i A
    exact (selection i).prefix_lt (by decide) A
  · intro i A
    exact (selection i).liftConstant_nonneg A
  · intro i A J
    exact (selection i).original_envelope (localPredicate i)
      (selection_excluded i) A J
  · intro i A
    exact (selection i).firstMoment_le A (n-16)

theorem directRow_nonneg (n m : ℕ) : 0 ≤ directRow n m :=
  fusionPhysicalDirectRow_nonneg (fun _ : Action => 8) action _ _ _
    (fun i A => (selection i).liftConstant_nonneg A) n m

theorem directRow_forward {n m : ℕ} (hnm : n ≤ m) : directRow n m = 0 :=
  fusionPhysicalDirectRow_forward (fun _ : Action => 8) action _ _ _
    (fun i A => (selection i).prefix_lt (by decide) A) hnm

/-- The same complete original-weight row has a positive exponential rate. -/
theorem directRow_decay :
    ∃ C kappa : ℝ, 0 < C ∧ 0 < kappa ∧ ∀ᶠ n : ℕ in atTop,
      ∑ m ∈ Finset.range n, directRow n m ≤
        C*(2:ℝ)^(-kappa*(n:ℝ)) :=
  fusionFiniteDirectRow_decay
    (fun j : FusionPhysicalMenuAxis (fun _ : Action => 8) action => 8)
    (fun j => (selection j.1).prefixDegree j.2)
    (fun j => (selection j.1).markerHalf j.2)
    (fun j => (selection j.1).liftConstant j.2)
    (fun j => fusionPhysicalMenuDivisor (fun _ : Action => 8) action j.1)
    (fun j => (selection j.1).gapParameter j.2)
    (fun j => (selection j.1).prefix_lt (by decide) j.2)
    (fun j => (selection j.1).prefix_eq_two_mul j.2)
    (fun j => (selection j.1).liftConstant_nonneg j.2)
    (fun j => fusionPhysicalMenuDivisor_pos (fun _ : Action => 8) action j.1)
    (fun j => (selection j.1).gapParameter_pos j.2)

theorem directRow_contractive :
    ∀ᶠ n : ℕ in atTop,
      ∑ m ∈ Finset.range n, directRow n m ≤ 1/2 :=
  fusionFiniteDirectRow_contractive
    (fun j : FusionPhysicalMenuAxis (fun _ : Action => 8) action => 8)
    (fun j => (selection j.1).prefixDegree j.2)
    (fun j => (selection j.1).markerHalf j.2)
    (fun j => (selection j.1).liftConstant j.2)
    (fun j => fusionPhysicalMenuDivisor (fun _ : Action => 8) action j.1)
    (fun j => (selection j.1).gapParameter j.2)
    (fun j => (selection j.1).prefix_lt (by decide) j.2)
    (fun j => (selection j.1).prefix_eq_two_mul j.2)
    (fun j => (selection j.1).liftConstant_nonneg j.2)
    (fun j => fusionPhysicalMenuDivisor_pos (fun _ : Action => 8) action j.1)
    (fun j => (selection j.1).gapParameter_pos j.2)

/-- Any first-owner or earlier-owner filter only decreases the same unmarked
direct family and therefore uses the identical row. -/
theorem filtered_direct_recurrence (n : ℕ) (hn : 16 ≤ n)
    (R : Subgroup (Equiv.Perm (Fin n)) → Prop) :
    (Nat.card {H : directFamily n // R H.1} : ℝ)/exactBenchmark n ≤
      ∑ m ∈ Finset.range n, directRow n m *
        ((subgroupCount m : ℝ)/exactBenchmark m) := by
  have hcard : Nat.card {H : directFamily n // R H.1} ≤ Nat.card (directFamily n) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  exact (div_le_div_of_nonneg_right (by exact_mod_cast hcard)
    (exactBenchmark_pos n).le).trans (direct_recurrence n hn)

end DegreeSixteen
end SymmetricSubgroupAsymptotics.BinaryDegree16NormalizerSaturatedDirect

end
