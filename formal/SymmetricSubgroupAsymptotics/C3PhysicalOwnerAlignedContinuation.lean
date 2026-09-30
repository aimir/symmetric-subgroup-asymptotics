import SymmetricSubgroupAsymptotics.C3PhysicalOwnerFiniteContinuation
import SymmetricSubgroupAsymptotics.RelativeAmbientTransport

/-!
# High-C3 continuation with the selected normal pair retained

The first-owner cover previously indexed a cell only by its width, global
owner branch, and abstract action class.  That was enough for set-theoretic
coverage, but it forgot that this particular action class was the orbit which
carried the strict high normal pair.  Branch-specific numerical estimates
could therefore not be applied safely to the enlarged canonical cell.

This file repairs that interface.  The refined finite index carries an actual
normal subgroup of the retained action, its strict high inequality, and the
intrinsic earlier-owner disjunction on that same action.  The physical cover
is rebuilt with the action chart still visible, and the forward continuation
is then assembled over only these certified cells.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- The selected retained action still carries the literal high normal pair
and the intrinsic earlier owner which caused this c=1 state to be removed. -/
def C3HighAlignedAction {w : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w))) : Prop :=
  ∃ (N : Subgroup U) (hN : N.Normal),
    letI := hN
    3 * w < 20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ∧
      TernaryHighEarlierOwner U (Fin w)

/-- The first-owner branch label is also certified on the selected action.
For the degree-six and degree-twelve branches this retains the exact width;
for the other two branches it retains the p-group or natural-A4 structure. -/
def C3HighAlignedOwnerAction {w : ℕ} (k : C3PhysicalOwnerKind)
    (U : Subgroup (Equiv.Perm (Fin w))) : Prop :=
  C3HighAlignedAction U ∧ k.property U (Fin w)

theorem C3PhysicalOwnerKind.property_relabel
    (k : C3PhysicalOwnerKind) {Ω Ξ : Type}
    (e : Ω ≃ Ξ) (A : Subgroup (Equiv.Perm Ω))
    (h : k.property A Ω) : k.property (relabelSubgroup e A) Ξ := by
  cases k with
  | ternaryPGroup =>
      exact h.of_equiv (e.permCongrHom.subgroupMap A)
  | naturalA4 =>
      exact TernaryHighEarlierOwner.naturalA4_relabel e A h
  | degreeSix =>
      change Nat.card Ξ = 6
      calc
        Nat.card Ξ = Nat.card Ω := (Nat.card_congr e).symm
        _ = 6 := h
  | degreeTwelve =>
      change Nat.card Ξ = 12
      calc
        Nat.card Ξ = Nat.card Ω := (Nat.card_congr e).symm
        _ = 12 := h

namespace C3HighNestedCarrier

/-- Transport the selected normal pair and its full-ambient invariant
characters through the exact action chart used by the fusion deletion. -/
theorem Data.alignedAction_of_chart
    {b w : ℕ}
    (H : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)))
    (C : Data H)
    (hw : Nat.card C.orbit.orbit = w)
    (hEarlier : TernaryHighEarlierOwner
      (OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) C.orbit)
      C.orbit.orbit)
    (U : Subgroup (Equiv.Perm (Fin w)))
    (e : Fin w ≃ C.orbit.orbit)
    (himage : relabelSubgroup e U =
      OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) C.orbit) :
    C3HighAlignedAction U := by
  let A := OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) C.orbit
  let g : U ≃* A :=
    (e.permCongrHom.subgroupMap U).trans (MulEquiv.subgroupCongr himage)
  let N : Subgroup U := C.normal.map g.symm.toMonoidHom
  have hN : N.Normal :=
    Subgroup.Normal.map C.normal_normal g.symm.toMonoidHom g.symm.surjective
  have hrel : relabelSubgroup e.symm A = U := by
    dsimp only [A]
    rw [← himage]
    exact relabelSubgroup_symm e U
  have hOwner : TernaryHighEarlierOwner U (Fin w) := by
    have h := TernaryHighEarlierOwner.relabel e.symm A hEarlier
    rwa [hrel] at h
  refine ⟨N, hN, ?_, hOwner⟩
  letI : C.normal.Normal := C.normal_normal
  letI : N.Normal := hN
  have hdim :=
    (relativeCharacterAmbientCongr 3 g.symm C.normal N rfl).finrank_eq
  simpa only [hw, hdim] using C.high

/-- The same chart transports the precise first-owner branch property as
well as the normal pair and the full earlier-owner witness. -/
theorem Data.alignedOwnerAction_of_chart
    {b w : ℕ}
    (H : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)))
    (C : Data H)
    (hw : Nat.card C.orbit.orbit = w)
    (hEarlier : TernaryHighEarlierOwner
      (OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) C.orbit)
      C.orbit.orbit)
    (k : C3PhysicalOwnerKind)
    (hk : k.property
      (OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) C.orbit)
      C.orbit.orbit)
    (U : Subgroup (Equiv.Perm (Fin w)))
    (e : Fin w ≃ C.orbit.orbit)
    (himage : relabelSubgroup e U =
      OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) C.orbit) :
    C3HighAlignedOwnerAction k U := by
  refine ⟨C.alignedAction_of_chart H hw hEarlier U e himage, ?_⟩
  have h := C3PhysicalOwnerKind.property_relabel k e.symm
    (OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) C.orbit) hk
  have hrel : relabelSubgroup e.symm
      (OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) C.orbit) = U := by
    rw [← himage]
    exact relabelSubgroup_symm e U
  rwa [hrel] at h

end C3HighNestedCarrier

/-- The finite first-owner index, now certified on the exact retained action
rather than only on the complete reconstructed subgroup. -/
abbrev C3HighAlignedFirstOwnerIndex :=
  {j : C3HighFirstOwnerIndex //
    C3HighAlignedOwnerAction (c3PhysicalOwnerKindEquiv j.2.1)
      (c3HighFirstOwnerAction j)}

def c3HighAlignedFirstOwnerWidth (j : C3HighAlignedFirstOwnerIndex) : ℕ :=
  c3HighFirstOwnerWidth j.1

def c3HighAlignedFirstOwnerAction (j : C3HighAlignedFirstOwnerIndex) :
    Subgroup (Equiv.Perm (Fin (c3HighAlignedFirstOwnerWidth j))) :=
  c3HighFirstOwnerAction j.1

def c3HighAlignedFirstOwnerPredicate
    (j : C3HighAlignedFirstOwnerIndex) (b : ℕ) :
    Subgroup (c3HighAlignedFirstOwnerAction j × Equiv.Perm (Fin b)) → Prop :=
  c3HighFirstOwnerPredicate j.1 b

theorem c3HighAlignedFirstOwnerWidth_pos (j : C3HighAlignedFirstOwnerIndex) :
    0 < c3HighAlignedFirstOwnerWidth j :=
  c3HighFirstOwnerWidth_pos j.1

theorem c3HighAlignedFirstOwnerWidth_le_of_twentySeven_le
    (n : ℕ) (hn : 27 ≤ n) (j : C3HighAlignedFirstOwnerIndex) :
    c3HighAlignedFirstOwnerWidth j ≤ n :=
  c3HighFirstOwnerWidth_le_of_twentySeven_le n hn j.1

theorem c3HighAlignedFirstOwnerPredicate_natural
    (j : C3HighAlignedFirstOwnerIndex) (b : ℕ) :
    FusionOrbitNatural (c3HighAlignedFirstOwnerAction j)
      (c3HighAlignedFirstOwnerPredicate j b) :=
  c3HighFirstOwnerPredicate_natural j.1 b

/-- The complete high-C3 owner is covered by aligned cells.  The action
class, high pair, and owner witness all come from the same selected orbit. -/
theorem c3PhysicalStructuralOwner_alignedFiniteFusionCover
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (n : ℕ) (hn : 27 ≤ n)
    (G : Subgroup (Equiv.Perm (Fin n)))
    (hG : G ∈ C3PhysicalStructuralOwnerSet n) :
    ∃ j : C3HighAlignedFirstOwnerIndex,
      G ∈ FusionWidthCanonicalFamily
        (c3HighAlignedFirstOwnerAction j)
        (c3HighAlignedFirstOwnerWidth_le_of_twentySeven_le n hn j)
        (c3HighAlignedFirstOwnerPredicate j
          (n - c3HighAlignedFirstOwnerWidth j)) := by
  obtain ⟨ownerEligible, hEligible⟩ :=
    c3PhysicalStructuralBranchMenu_cover
      hChief hWeight hPrimitive h18 hG.2.1
  obtain ⟨owner, howner⟩ := firstOwned_exists
    (c3PatternStructuralBranchMenu n) G
      ⟨ownerEligible, hEligible, hG.2.2⟩
  rcases howner.1.1 with ⟨b, e, H, hphysical, o, N, hN,
    hHigh, hEarlier, hk⟩
  let A := OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o
  letI : MulAction.IsPretransitive A o.orbit :=
    orbitImage_pretransitive (C3ComplementSource b H) o
  letI : N.Normal := hN
  have hdegrees : Nat.card o.orbit = 3 ∨ Nat.card o.orbit = 4 ∨
      Nat.card o.orbit = 6 ∨ Nat.card o.orbit = 9 ∨
      Nat.card o.orbit = 12 ∨ Nat.card o.orbit = 27 :=
    ternaryHigh_action_degree_menu
      hChief hWeight hPrimitive h18 N hHigh
  obtain ⟨d, hd⟩ := C3HighWidthLabel.exists_of_degree_menu hdegrees
  have hdegree : b + 3 = n := by
    have hcard := Nat.card_congr e
    have hternary : Nat.card TernaryCyclic = 3 := by
      rw [Nat.card_congr RepeatedMarkerOwnerBound.ternaryFinEquiv,
        Nat.card_fin]
    rw [Nat.card_sum, hternary, Nat.card_fin, Nat.card_fin] at hcard
    omega
  subst n
  let C : C3HighNestedCarrier.Data H := ⟨o, N, hN, hHigh⟩
  have hordinary' : ¬ IsCriticalSubgroup (b + 3)
      (relabelSubgroup e (C3HighNestedCarrier.physicalSubgroup H)) := by
    rw [hphysical]
    exact hG.1
  have howner' : FirstOwned (c3PatternStructuralBranchMenu (b + 3)) owner
      (relabelSubgroup e (C3HighNestedCarrier.physicalSubgroup H)) := by
    rwa [hphysical]
  have hnon2 : ¬ IsPGroup 2 A := by
    exact strict_ternaryRelativeHead_not_isPGroup_two N hHigh
  obtain ⟨i, eO, himage⟩ := Non2TransitiveActionClass.orbit_cover
    (C3ComplementSource b H) o hd.symm hnon2
  have haligned : C3HighAlignedOwnerAction
      (c3PhysicalOwnerKindEquiv owner) i.representative :=
    C.alignedOwnerAction_of_chart H hd.symm hEarlier
      (c3PhysicalOwnerKindEquiv owner) hk i.representative eO himage
  let j0 : C3HighFirstOwnerIndex := ⟨d, owner, i⟩
  let j : C3HighAlignedFirstOwnerIndex := ⟨j0, by
    simpa only [j0, c3HighFirstOwnerAction] using haligned⟩
  have hmem := C.mem_non2FirstOwnerCanonicalFamily_forAction
    c3PatternStructuralBranchMenu c3PatternStructuralBranchMenu_natural
      H hd.symm e hordinary' owner howner' i eO himage
  refine ⟨j, ?_⟩
  simpa only [j, j0, c3HighAlignedFirstOwnerAction,
    c3HighAlignedFirstOwnerWidth, c3HighAlignedFirstOwnerPredicate,
    c3HighFirstOwnerAction, c3HighFirstOwnerWidth,
    c3HighFirstOwnerPredicate, hphysical] using hmem

/-- Pointwise estimates for the certified cells assemble at the literal
deleted complement degree. -/
theorem c3PhysicalStructuralOwnerRatio_le_alignedForwardRow
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (f : C3HighAlignedFirstOwnerIndex → ℕ → ℝ)
    (hlocal : ∀ (j : C3HighAlignedFirstOwnerIndex) (n : ℕ)
      (hn : c3HighAlignedFirstOwnerWidth j ≤ n),
      (Nat.card (FusionWidthCanonicalFamily
        (c3HighAlignedFirstOwnerAction j) hn
        (c3HighAlignedFirstOwnerPredicate j
          (n - c3HighAlignedFirstOwnerWidth j))) : ℝ) /
          exactBenchmark n ≤
        f j (n - c3HighAlignedFirstOwnerWidth j) *
          ordinarySubgroupRatio (n - c3HighAlignedFirstOwnerWidth j))
    (n : ℕ) (hn : 27 ≤ n) :
    c3PhysicalStructuralOwnerRatio n ≤
      ∑ b ∈ Finset.range n,
        fusionForwardRow c3HighAlignedFirstOwnerWidth f n b *
          ordinarySubgroupRatio b := by
  let widthLe : ∀ j : C3HighAlignedFirstOwnerIndex,
      c3HighAlignedFirstOwnerWidth j ≤ n :=
    c3HighAlignedFirstOwnerWidth_le_of_twentySeven_le n hn
  have hcard := fusionPhysicalUnion_card_le
    (C3PhysicalStructuralOwnerSet n)
    (fun j : C3HighAlignedFirstOwnerIndex =>
      FusionWidthCanonicalFamily (c3HighAlignedFirstOwnerAction j) (widthLe j)
        (c3HighAlignedFirstOwnerPredicate j
          (n - c3HighAlignedFirstOwnerWidth j)))
    (c3PhysicalStructuralOwner_alignedFiniteFusionCover
      hChief hWeight hPrimitive h18 n hn)
  have hcardR : (Nat.card (C3PhysicalStructuralOwnerSet n) : ℝ) ≤
      ∑ j : C3HighAlignedFirstOwnerIndex,
        (Nat.card (FusionWidthCanonicalFamily
          (c3HighAlignedFirstOwnerAction j) (widthLe j)
          (c3HighAlignedFirstOwnerPredicate j
            (n - c3HighAlignedFirstOwnerWidth j))) : ℝ) := by
    exact_mod_cast hcard
  have hsum :
      ∑ j : C3HighAlignedFirstOwnerIndex,
          (Nat.card (FusionWidthCanonicalFamily
            (c3HighAlignedFirstOwnerAction j) (widthLe j)
            (c3HighAlignedFirstOwnerPredicate j
              (n - c3HighAlignedFirstOwnerWidth j))) : ℝ) /
            exactBenchmark n ≤
        ∑ j : C3HighAlignedFirstOwnerIndex,
          f j (n - c3HighAlignedFirstOwnerWidth j) *
            ordinarySubgroupRatio (n - c3HighAlignedFirstOwnerWidth j) := by
    apply Finset.sum_le_sum
    intro j _
    exact hlocal j n (widthLe j)
  have hrow := fusionForwardRow_weighted_sum
    c3HighAlignedFirstOwnerWidth f c3HighAlignedFirstOwnerWidth_pos
    ordinarySubgroupRatio n widthLe
  calc
    c3PhysicalStructuralOwnerRatio n ≤
        (∑ j : C3HighAlignedFirstOwnerIndex,
          (Nat.card (FusionWidthCanonicalFamily
            (c3HighAlignedFirstOwnerAction j) (widthLe j)
            (c3HighAlignedFirstOwnerPredicate j
              (n - c3HighAlignedFirstOwnerWidth j))) : ℝ)) /
          exactBenchmark n :=
      div_le_div_of_nonneg_right hcardR (exactBenchmark_pos n).le
    _ = ∑ j : C3HighAlignedFirstOwnerIndex,
        (Nat.card (FusionWidthCanonicalFamily
          (c3HighAlignedFirstOwnerAction j) (widthLe j)
          (c3HighAlignedFirstOwnerPredicate j
            (n - c3HighAlignedFirstOwnerWidth j))) : ℝ) /
          exactBenchmark n := Finset.sum_div _ _ _
    _ ≤ ∑ j : C3HighAlignedFirstOwnerIndex,
        f j (n - c3HighAlignedFirstOwnerWidth j) *
          ordinarySubgroupRatio (n - c3HighAlignedFirstOwnerWidth j) := hsum
    _ = _ := hrow.symm

/-- Exponentially decaying estimates on the aligned cells give the complete
high-C3 structural-owner continuation. -/
noncomputable def c3PhysicalStructuralOwner_alignedExponentialForwardEstimate
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (f : C3HighAlignedFirstOwnerIndex → ℕ → ℝ)
    (hf : ∀ j b, 0 ≤ f j b)
    (hdecay : ∀ j, ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧
      ∀ᶠ b : ℕ in atTop, f j b ≤ C * (2 : ℝ) ^ (-κ * (b : ℝ)))
    (hlocal : ∀ (j : C3HighAlignedFirstOwnerIndex) (n : ℕ)
      (hn : c3HighAlignedFirstOwnerWidth j ≤ n),
      (Nat.card (FusionWidthCanonicalFamily
        (c3HighAlignedFirstOwnerAction j) hn
        (c3HighAlignedFirstOwnerPredicate j
          (n - c3HighAlignedFirstOwnerWidth j))) : ℝ) /
          exactBenchmark n ≤
        f j (n - c3HighAlignedFirstOwnerWidth j) *
          ordinarySubgroupRatio (n - c3HighAlignedFirstOwnerWidth j)) :
    OrdinaryFrontierClosure.ExponentialForwardEstimate
      c3PhysicalStructuralOwnerRatio := by
  let W := fusionForwardRow_decay c3HighAlignedFirstOwnerWidth f
    c3HighAlignedFirstOwnerWidth_pos hdecay
  let C : ℝ := Classical.choose W
  have hCκ := Classical.choose_spec W
  let κ : ℝ := Classical.choose hCκ
  have hspec := Classical.choose_spec hCκ
  let V := eventually_atTop.mp hspec.2.2
  let N : ℕ := Classical.choose V
  have hN := Classical.choose_spec V
  refine
    { scalar := fun _ => 0
      kernel := fusionForwardRow c3HighAlignedFirstOwnerWidth f
      threshold := max 27 N
      rate := κ
      scalarConst := 1
      rowConst := C
      rate_pos := hspec.2.1
      scalarConst_pos := by norm_num
      rowConst_nonneg := hspec.1.le
      kernel_nonneg := ?_
      recurrence := ?_
      scalar_decay := ?_
      row_decay := ?_ }
  · intro n _ b _
    exact fusionForwardRow_nonneg c3HighAlignedFirstOwnerWidth f hf n b
  · intro n hn
    have hn27 : 27 ≤ n := (le_max_left 27 N).trans hn
    exact (c3PhysicalStructuralOwnerRatio_le_alignedForwardRow
      hChief hWeight hPrimitive h18 f hlocal n hn27).trans_eq
        (zero_add _).symm
  · intro n _
    positivity
  · intro n hn
    exact hN n ((le_max_right 27 N).trans hn)

end SymmetricSubgroupAsymptotics

end
