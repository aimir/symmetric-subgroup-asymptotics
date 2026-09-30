import SymmetricSubgroupAsymptotics.BinaryDegreeEightDirectEntryCoverage
import SymmetricSubgroupAsymptotics.BinaryOriginalWeightedPartialSelection
import SymmetricSubgroupAsymptotics.FusionActualOrbitCharts

/-!
# Normalizer-saturated direct ownership in degree eight

An actual binary orbit of size eight has a literal faithful restriction action
and a literal Goursat axis in the complete orbit/complement model.  The finite
degree-eight theorem sends that axis either to an original-weight direct entry
or to an exact carrier route.

Direct-entry existence is intrinsic and stable under every automorphism of the
literal action.  It therefore defines a normalizer-natural partial selection:
accepted axes carry their entry and all other axes have an empty surviving
fibre.  The selected orbit, point, chart, normal axis and carrier route remain
existential witnesses; the only objects counted below are the original
subgroups of the ambient symmetric group.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical Pointwise

namespace SymmetricSubgroupAsymptotics.BinaryDegreeEightNormalizerSaturatedDirect

open SymmetricSubgroupAsymptotics
open BinaryDegreeEightDirectEntryCoverage
open BinaryDegreeEightPhysicalAnalyticClosure

/-! ## Intrinsic entry existence and normalizer saturation -/

/-- Existence of a direct entry on a raw axis, retaining a proof that the axis
is normal.  This makes the predicate available before a Goursat normality
proof has been installed as a typeclass instance. -/
def HasWeightedEntryAxis (U : Subgroup (Equiv.Perm (Fin 8)))
    (N : Subgroup U) : Prop :=
  ∃ hN : N.Normal, Nonempty (@DirectEntry8 U N hN)

/-- Direct-entry existence is invariant under every equivalence of literal
eight-point action groups. -/
theorem hasWeightedEntryAxis_map
    {U V : Subgroup (Equiv.Perm (Fin 8))} (e : U ≃* V)
    {N : Subgroup U} (H : HasWeightedEntryAxis U N) :
    HasWeightedEntryAxis V (N.map e.toMonoidHom) := by
  obtain ⟨hN,⟨E⟩⟩ := H
  let hM : (N.map e.toMonoidHom).Normal :=
    Subgroup.Normal.map hN e.toMonoidHom e.surjective
  refine ⟨hM,?_⟩
  letI : N.Normal := hN
  letI : (N.map e.toMonoidHom).Normal := hM
  exact ⟨BinaryOriginalWeightedDirectEntry.transport e rfl E⟩

/-- On a packaged normal, existential normality can be replaced by the
packaged instance without changing the entry type. -/
theorem nonemptyEntry_of_hasWeightedEntryAxis
    {U : Subgroup (Equiv.Perm (Fin 8))}
    (A : {N : Subgroup U // N.Normal})
    (H : HasWeightedEntryAxis U A.1) : Nonempty (DirectEntry8 U A.1) := by
  obtain ⟨hN,hE⟩ := H
  letI : A.1.Normal := hN
  simpa only using hE

/-! ## Actual eight-point orbit models -/

/-- An intrinsic eight-point orbit of the original subgroup, together with
binaryity of its actual faithful restriction image. -/
structure OrbitWitness {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n))) where
  point : Fin n
  orbit_card : Nat.card (MulAction.orbit H point) = 8
  binary : IsPGroup 2 (FusionActualOrbitCharts.orbitImage H point)

namespace OrbitWitness

variable {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))} (W : OrbitWitness H)

def chart : Fin 8 ⊕ Fin (n-8) ≃ Fin n :=
  FusionActualOrbitCharts.chart H W.point W.orbit_card

def action : Subgroup (Equiv.Perm (Fin 8)) :=
  FusionActualOrbitCharts.chartAction H W.point W.orbit_card

def pulled : Subgroup (Equiv.Perm (Fin 8 ⊕ Fin (n-8))) :=
  relabelSubgroup W.chart.symm H

/-- The complete exterior model; every correlation with the complement is
retained. -/
def model : Subgroup (W.action × Equiv.Perm (Fin (n-8))) :=
  fusionDeletedModel W.action W.pulled

include W in
theorem degree_le : 8 ≤ n :=
  FusionActualOrbitCharts.degree_le H W.point W.orbit_card

theorem action_binary : IsPGroup 2 W.action :=
  FusionActualOrbitCharts.chartAction_isPGroup H W.point W.orbit_card 2 W.binary

instance action_pretransitive : MulAction.IsPretransitive W.action (Fin 8) :=
  FusionActualOrbitCharts.chartAction_transitive H W.point W.orbit_card

theorem pulled_preserves :
    ∀ k ∈ W.pulled,
      Set.MapsTo k (Set.range (Sum.inl : Fin 8 → Fin 8 ⊕ Fin (n-8)))
        (Set.range (Sum.inl : Fin 8 → Fin 8 ⊕ Fin (n-8))) :=
  FusionActualOrbitCharts.chart_preserves H W.point W.orbit_card

theorem first_projection :
    (fusionPhysicalBlockPullback W.pulled).map
      (MonoidHom.fst (Equiv.Perm (Fin 8)) (Equiv.Perm (Fin (n-8)))) = W.action :=
  rfl

theorem model_full :
    W.model.map (MonoidHom.fst W.action (Equiv.Perm (Fin (n-8)))) = ⊤ :=
  fusionDeletedModel_full W.action W.pulled W.first_projection

def axis : Subgroup W.action := W.model.goursatFst

instance axis_normal : W.axis.Normal :=
  Subgroup.normal_goursatFst (by
    intro u
    have hu : u ∈ W.model.map
        (MonoidHom.fst W.action (Equiv.Perm (Fin (n-8)))) := by
      rw [W.model_full]
      trivial
    obtain ⟨x,hx,he⟩ := hu
    exact ⟨⟨x,hx⟩,he⟩)

/-- The literal physical axis reaches either the common weighted entry or an
exact carrier owner. -/
theorem weighted_or_carrier :
    Nonempty (DirectEntry8 W.action W.axis) ∨
      CarrierOwner W.action W.axis :=
  complete_axis_weighted_or_carrier W.action W.action_binary
    (by
      intro x y
      obtain ⟨g,hg⟩ := MulAction.exists_smul_eq W.action x y
      exact ⟨g,g.property,hg⟩) W.axis

theorem model_recovers :
    W.model.map (fusionOrbitAction W.action) = W.pulled :=
  fusionDeletedModel_recovers W.action W.pulled W.pulled_preserves W.first_projection

theorem recovers_original :
    relabelSubgroup W.chart (W.model.map (fusionOrbitAction W.action)) = H := by
  rw [W.model_recovers]
  simp only [pulled,relabelSubgroup_trans,Equiv.symm_trans_self,
    relabelSubgroup_refl]

end OrbitWitness

/-! ## Unmarked direct and carrier families -/

/-- Membership records only the existence of an actual binary orbit of size
eight. -/
def physicalFamily (n : ℕ) : Set (Subgroup (Equiv.Perm (Fin n))) :=
  {H | Nonempty (OrbitWitness H)}

/-- At least one literal eight-point orbit axis has a weighted direct entry.
The witness is existential and creates no counted marking. -/
def directFamily (n : ℕ) : Set (Subgroup (Equiv.Perm (Fin n))) :=
  {H | ∃ W : OrbitWitness H, Nonempty (DirectEntry8 W.action W.axis)}

/-- The exact complement of the intrinsic direct family inside the physical
eight-orbit sector. -/
def carrierResidualFamily (n : ℕ) : Set (Subgroup (Equiv.Perm (Fin n))) :=
  {H | H ∈ physicalFamily n ∧ H ∉ directFamily n}

theorem directFamily_subset (n : ℕ) : directFamily n ⊆ physicalFamily n := by
  rintro H ⟨W,_⟩
  exact ⟨W⟩

/-- Every possible eligible witness of a residual subgroup is a carrier
witness.  Thus a choice of point, chart or route is never counted. -/
theorem carrierResidual_all_witnesses {n : ℕ}
    {H : Subgroup (Equiv.Perm (Fin n))}
    (hH : H ∈ carrierResidualFamily n) (W : OrbitWitness H) :
    CarrierOwner W.action W.axis := by
  rcases W.weighted_or_carrier with hentry | hcarrier
  · exact False.elim (hH.2 ⟨W,hentry⟩)
  · exact hcarrier

/-- The same all-witness statement in the exact routed-carrier interface. -/
theorem carrierResidual_all_routed {n : ℕ}
    {H : Subgroup (Equiv.Perm (Fin n))}
    (hH : H ∈ carrierResidualFamily n) (W : OrbitWitness H) :
    Nonempty (RoutedCarrier W.action W.axis) :=
  (carrierResidual_all_witnesses hH W).routed

/-- Every residual witness also retains its exact pulled-back axis slot and
support classification. -/
theorem carrierResidual_all_classified_slots {n : ℕ}
    {H : Subgroup (Equiv.Perm (Fin n))}
    (hH : H ∈ carrierResidualFamily n) (W : OrbitWitness H) :
    Nonempty {S : AxisSlot W.action W.axis // S.HasNoncritical ∨ S.IsPureE8} :=
  (carrierResidual_all_witnesses hH W).classifiedAxisSlot

theorem direct_or_carrierResidual {n : ℕ}
    {H : Subgroup (Equiv.Perm (Fin n))} (hH : H ∈ physicalFamily n) :
    H ∈ directFamily n ∨ H ∈ carrierResidualFamily n := by
  by_cases hdirect : H ∈ directFamily n
  · exact Or.inl hdirect
  · exact Or.inr ⟨hH,hdirect⟩

/-- Family-level upper partition on original subgroups.  No orbit, axis or
carrier route is charged as a marking. -/
theorem physical_card_le_direct_add_carrierResidual (n : ℕ) :
    Nat.card (physicalFamily n) ≤
      Nat.card (directFamily n) + Nat.card (carrierResidualFamily n) := by
  let A : Bool → Set (Subgroup (Equiv.Perm (Fin n))) := fun b =>
    if b then carrierResidualFamily n else directFamily n
  have h := fusionPhysicalUnion_card_le (physicalFamily n) A (by
    intro H hH
    rcases direct_or_carrierResidual hH with hd | hc
    · exact ⟨false,hd⟩
    · exact ⟨true,hc⟩)
  simpa [A,add_comm] using h

/-! ## The saturated partial selection -/

/-- All literal transitive binary actions on eight points. -/
abbrev Action :=
  {U : Subgroup (Equiv.Perm (Fin 8)) //
    IsPGroup 2 U ∧ MulAction.IsPretransitive U (Fin 8)}

instance actionFintype : Fintype Action := Fintype.ofFinite _

def action (i : Action) : Subgroup (Equiv.Perm (Fin 8)) := i.1

theorem action_binary (i : Action) : IsPGroup 2 (action i) := i.2.1

theorem action_transitive (i : Action) :
    MulAction.IsPretransitive (action i) (Fin 8) := i.2.2

/-- Select exactly the intrinsic direct axes.  The choice is fixed before the
exterior degree and exterior subgroup. -/
def selection (i : Action) :
    BinaryOriginalWeightedPartialSelection (h := 4) (action i) where
  Active := HasWeightedEntryAxis (action i)
  active_natural := by
    intro c N hN
    exact hasWeightedEntryAxis_map ((action i).normalizerMonoidHom c) hN
  entry := by
    intro A hA
    exact Classical.choice (nonemptyEntry_of_hasWeightedEntryAxis A hA)

def localPredicate {b : ℕ} (i : Action)
    (K : Subgroup (action i × Equiv.Perm (Fin b))) : Prop :=
  (selection i).predicate K

theorem localPredicate_natural {b : ℕ} (i : Action) :
    FusionOrbitNatural (action i) (localPredicate (b := b) i) :=
  (selection i).predicate_natural

/-- The complete original-action row for the normalizer-saturated direct
sector.  Inactive axes have literal zero coefficients. -/
def directRow (n m : ℕ) : ℝ :=
  fusionPhysicalDirectRow (fun _ : Action => 4) action
    (fun i A => (selection i).prefixDegree A)
    (fun i A => (selection i).liftConstant A)
    (fun i A => (selection i).gapParameter A) n m

/-- An unmarked direct witness enters the canonical family of its actual
literal restriction action. -/
theorem directFamily_cover {n : ℕ} (hn : 8 ≤ n)
    (H : Subgroup (Equiv.Perm (Fin n))) (hH : H ∈ directFamily n) :
    ∃ i : Action,
      H ∈ FusionCanonicalFamily (h := 4) (action i) hn (localPredicate i) := by
  obtain ⟨W,hentry⟩ := hH
  let i : Action := ⟨W.action,W.action_binary,inferInstance⟩
  refine ⟨i,?_⟩
  apply fusionCanonicalFamily_of_chart (h := 4) (action i) hn H W.chart
    W.pulled_preserves W.first_projection (localPredicate i)
  change HasWeightedEntryAxis W.action W.axis
  exact ⟨W.axis_normal,hentry⟩

/-- Exact ordinary-count forward recurrence for the unmarked direct family. -/
theorem direct_recurrence (n : ℕ) (hn : 8 ≤ n) :
    (Nat.card (directFamily n) : ℝ)/exactBenchmark n ≤
      ∑ m ∈ Finset.range n, directRow n m *
        ((subgroupCount m : ℝ)/exactBenchmark m) := by
  unfold directRow
  apply fusionPhysicalUnion_direct_recurrence
    (fun _ : Action => 4) action n (fun _ => hn) (directFamily n)
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
    exact (selection i).original_envelope A J
  · intro i A
    simpa only [pow_one,one_mul] using (selection i).moment_le A (n-8) 1

theorem directRow_nonneg (n m : ℕ) : 0 ≤ directRow n m :=
  fusionPhysicalDirectRow_nonneg (fun _ : Action => 4) action _ _ _
    (fun i A => (selection i).liftConstant_nonneg A) n m

theorem directRow_forward {n m : ℕ} (hnm : n ≤ m) : directRow n m = 0 :=
  fusionPhysicalDirectRow_forward (fun _ : Action => 4) action _ _ _
    (fun i A => (selection i).prefix_lt (by decide) A) hnm

/-- The exact direct row has a positive exponential decay rate. -/
theorem directRow_decay :
    ∃ C kappa : ℝ, 0 < C ∧ 0 < kappa ∧ ∀ᶠ n : ℕ in atTop,
      ∑ m ∈ Finset.range n, directRow n m ≤
        C*(2:ℝ)^(-kappa*(n:ℝ)) :=
  fusionFiniteDirectRow_decay
    (fun j : FusionPhysicalMenuAxis (fun _ : Action => 4) action => 4)
    (fun j => (selection j.1).prefixDegree j.2)
    (fun j => (selection j.1).markerHalf j.2)
    (fun j => (selection j.1).liftConstant j.2)
    (fun j => fusionPhysicalMenuDivisor (fun _ : Action => 4) action j.1)
    (fun j => (selection j.1).gapParameter j.2)
    (fun j => (selection j.1).prefix_lt (by decide) j.2)
    (fun j => (selection j.1).prefix_eq_two_mul j.2)
    (fun j => (selection j.1).liftConstant_nonneg j.2)
    (fun j => fusionPhysicalMenuDivisor_pos (fun _ : Action => 4) action j.1)
    (fun j => (selection j.1).gapParameter_pos j.2)

theorem directRow_contractive :
    ∀ᶠ n : ℕ in atTop,
      ∑ m ∈ Finset.range n, directRow n m ≤ 1/2 :=
  fusionFiniteDirectRow_contractive
    (fun j : FusionPhysicalMenuAxis (fun _ : Action => 4) action => 4)
    (fun j => (selection j.1).prefixDegree j.2)
    (fun j => (selection j.1).markerHalf j.2)
    (fun j => (selection j.1).liftConstant j.2)
    (fun j => fusionPhysicalMenuDivisor (fun _ : Action => 4) action j.1)
    (fun j => (selection j.1).gapParameter j.2)
    (fun j => (selection j.1).prefix_lt (by decide) j.2)
    (fun j => (selection j.1).prefix_eq_two_mul j.2)
    (fun j => (selection j.1).liftConstant_nonneg j.2)
    (fun j => fusionPhysicalMenuDivisor_pos (fun _ : Action => 4) action j.1)
    (fun j => (selection j.1).gapParameter_pos j.2)

/-- Any first-owner or earlier-owner filter decreases the same intrinsic
unmarked family and therefore uses the identical forward row. -/
theorem filtered_direct_recurrence (n : ℕ) (hn : 8 ≤ n)
    (R : Subgroup (Equiv.Perm (Fin n)) → Prop) :
    (Nat.card {H : directFamily n // R H.1} : ℝ)/exactBenchmark n ≤
      ∑ m ∈ Finset.range n, directRow n m *
        ((subgroupCount m : ℝ)/exactBenchmark m) := by
  have hcard : Nat.card {H : directFamily n // R H.1} ≤
      Nat.card (directFamily n) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  exact (div_le_div_of_nonneg_right (by exact_mod_cast hcard)
    (exactBenchmark_pos n).le).trans (direct_recurrence n hn)

end SymmetricSubgroupAsymptotics.BinaryDegreeEightNormalizerSaturatedDirect

end
