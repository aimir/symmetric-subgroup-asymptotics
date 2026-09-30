import SymmetricSubgroupAsymptotics.Non2PreE7NoPairNoC3EarlierOwnerCatalogue
import SymmetricSubgroupAsymptotics.Non2PreE7NonPairConcreteInterface
import SymmetricSubgroupAsymptotics.Non2PreE7NoPairNoC3AdditiveTailInterface
import SymmetricSubgroupAsymptotics.C1DegreeNineSourcePatternRelabel
import SymmetricSubgroupAsymptotics.RepeatedMarkerOwnerBound

/-!
# Restricting the earlier-owner envelopes to the no-C3 source

The 53 historical earlier owners were inserted before the complete regular-
`C3` family was partitioned out.  Their local counting theorems therefore
have the broader pre-`E7`, non-pair complete-source predicate as domain.

This file proves the common restriction step once.  The no-pair/no-`C3`
predicate is a literal subtype of the broader predicate, so every checked
direct owner envelope remains valid with the same comparator group, faithful
action, and numerical parameters.  No owner label is turned into a predicate
here: the predicates supplied by the broad concrete catalogue are retained
verbatim.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- Restricting a complete-source predicate can only decrease the literal
surviving-epimorphism count on an unchanged action and normal axis. -/
theorem fusionSurvivingEpiCount_mono
    {w b : ℕ} {U : Subgroup (Equiv.Perm (Fin w))}
    {P Q : Subgroup (U × Equiv.Perm (Fin b)) → Prop}
    (hPQ : ∀ H, P H → Q H)
    (N : {N : Subgroup U // N.Normal})
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount U P N J ≤
      fusionSurvivingEpiCount U Q N J := by
  unfold fusionSurvivingEpiCount
  let f : {beta : GroupEpimorphism J (U ⧸ N.1) //
      P (fusionFullGoursatEncode N J beta).1} →
      {beta : GroupEpimorphism J (U ⧸ N.1) //
        Q (fusionFullGoursatEncode N J beta).1} :=
    fun beta => ⟨beta.1, hPQ _ beta.2⟩
  have hf : Function.Injective f := by
    intro beta gamma h
    apply Subtype.ext
    simpa only [f] using congrArg
      (fun x : {delta : GroupEpimorphism J (U ⧸ N.1) //
        Q (fusionFullGoursatEncode N J delta).1} => x.1) h
  exact_mod_cast Nat.card_le_card_of_injective f hf

namespace Non2UnipotentPrefixFiniteMenu

open RepeatedMarkerOwnerBound

/-! ## Certificate-defined family predicates -/

/-- One literal orbit carrying a certificate of the indicated historical
family.  The action is a genuine pre-`E7`, non-pair action class on its
original points.  Keeping the orbit and its chart in the witness is what lets
the physical cover select this orbit, instead of selecting an unrelated bad
orbit after ownership has been decided. -/
structure PreE7EarlierFamilyOrbit
    (FamilyAction : PreE7NoPairNoC3EarlierOwnerFamily →
      ∀ w, PreE7NonPairActionClass w → Prop)
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n))) where
  width : ℕ
  action : PreE7NonPairActionClass width
  applies : FamilyAction family width action
  width_three : 3 ≤ width
  orbit : OrbitProfileFromOrbits.Orbit H
  chart : Fin width ≃ orbit.orbit
  action_eq : relabelSubgroup chart (preE7NonPairAction width action) =
    OrbitProfileFromOrbits.orbitImage H orbit

namespace PreE7EarlierFamilyOrbit

/-- A family-orbit certificate is transported by an ambient relabelling with
the same historical family and the same original action class. -/
def relabel
    {FamilyAction : PreE7NoPairNoC3EarlierOwnerFamily →
      ∀ w, PreE7NonPairActionClass w → Prop}
    {family : PreE7NoPairNoC3EarlierOwnerFamily}
    {m n : ℕ} {H : Subgroup (Equiv.Perm (Fin m))}
    (W : PreE7EarlierFamilyOrbit FamilyAction family H)
    (e : Fin m ≃ Fin n) :
    PreE7EarlierFamilyOrbit FamilyAction family (relabelSubgroup e H) where
  width := W.width
  action := W.action
  applies := W.applies
  width_three := W.width_three
  orbit := OrbitProfileFromOrbits.relabelOrbit e H W.orbit
  chart := W.chart.trans
    (OrbitProfileFromOrbits.relabelOrbitEquiv e H W.orbit)
  action_eq := by
    rw [← relabelSubgroup_trans, W.action_eq]
    exact OrbitProfileFromOrbits.relabel_orbitImage_relabelOrbit e H W.orbit

end PreE7EarlierFamilyOrbit

/-- The actual mathematical earlier-owner predicate: the complete physical
subgroup has a literal orbit carrying a certificate for this family.  The
historical label by itself is never used as a predicate. -/
def preE7NoPairNoC3EarlierFamilyPredicate
    (FamilyAction : PreE7NoPairNoC3EarlierOwnerFamily →
      ∀ w, PreE7NonPairActionClass w → Prop)
    (n : ℕ) (i : Fin preE7NoPairNoC3EarlierOwnerCount)
    (H : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  Nonempty (PreE7EarlierFamilyOrbit FamilyAction
    (preE7NoPairNoC3EarlierOwnerEquiv i) H)

/-- Certificate-defined family predicates are invariant under every change
of the ambient point labels, including the cross-degree cast used by the
selected-orbit chart. -/
theorem preE7NoPairNoC3EarlierFamilyPredicate_natural
    (FamilyAction : PreE7NoPairNoC3EarlierOwnerFamily →
      ∀ w, PreE7NonPairActionClass w → Prop) :
    DegreeNaturalOwnerMenu
      (preE7NoPairNoC3EarlierFamilyPredicate FamilyAction) := by
  intro m n hmn e i H
  subst n
  constructor
  · rintro ⟨W⟩
    have W' := W.relabel e.symm
    exact ⟨by simpa only [relabelSubgroup_symm] using W'⟩
  · rintro ⟨W⟩
    exact ⟨W.relabel e⟩

/-- On an earlier branch the displayed original action must carry the same
family certificate.  The appended terminal branch accepts every displayed
action; its global first-owner condition already says that no earlier family
orbit exists. -/
def preE7NoPairNoC3SelectedActionEligible
    (FamilyAction : PreE7NoPairNoC3EarlierOwnerFamily →
      ∀ w, PreE7NonPairActionClass w → Prop)
    (w : ℕ)
    (j : PreE7NonPairFirstOwnerIndex
      (preE7NoPairNoC3EarlierOwnerCount + 1) w) : Prop :=
  if h : j.1.val < preE7NoPairNoC3EarlierOwnerCount then
    FamilyAction
      (preE7NoPairNoC3EarlierOwnerEquiv ⟨j.1.val, h⟩) w j.2
  else True

@[simp] theorem preE7NoPairNoC3SelectedActionEligible_castSucc
    (FamilyAction : PreE7NoPairNoC3EarlierOwnerFamily →
      ∀ w, PreE7NonPairActionClass w → Prop)
    {w : ℕ} (i : Fin preE7NoPairNoC3EarlierOwnerCount)
    (U : PreE7NonPairActionClass w) :
    preE7NoPairNoC3SelectedActionEligible FamilyAction w (i.castSucc, U) ↔
      FamilyAction (preE7NoPairNoC3EarlierOwnerEquiv i) w U := by
  simp [preE7NoPairNoC3SelectedActionEligible]

@[simp] theorem preE7NoPairNoC3SelectedActionEligible_last
    (FamilyAction : PreE7NoPairNoC3EarlierOwnerFamily →
      ∀ w, PreE7NonPairActionClass w → Prop)
    {w : ℕ} (U : PreE7NonPairActionClass w) :
    preE7NoPairNoC3SelectedActionEligible FamilyAction w
      (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) := by
  simp [preE7NoPairNoC3SelectedActionEligible]

/-- The first-owner source with the indispensable local action check.  This
prevents a subgroup owned through one family orbit from being charged through
an unrelated displayed orbit. -/
def preE7NoPairNoC3CertifiedFirstOwnerPredicate
    (FamilyAction : PreE7NoPairNoC3EarlierOwnerFamily →
      ∀ w, PreE7NonPairActionClass w → Prop)
    (w : ℕ)
    (j : PreE7NonPairFirstOwnerIndex
      (preE7NoPairNoC3EarlierOwnerCount + 1) w)
    (b : ℕ)
    (H : Subgroup
      (preE7NonPairFirstOwnerAction w j × Equiv.Perm (Fin b))) : Prop :=
  preE7NoPairNoC3FirstOwnerPredicate
      (ownerOrResidualEligible
        (preE7NoPairNoC3EarlierFamilyPredicate FamilyAction)) w j b H ∧
    preE7NoPairNoC3SelectedActionEligible FamilyAction w j

theorem preE7NoPairNoC3CertifiedFirstOwnerPredicate_natural
    (FamilyAction : PreE7NoPairNoC3EarlierOwnerFamily →
      ∀ w, PreE7NonPairActionClass w → Prop)
    (w : ℕ)
    (j : PreE7NonPairFirstOwnerIndex
      (preE7NoPairNoC3EarlierOwnerCount + 1) w)
    (b : ℕ) :
    FusionOrbitNatural (preE7NonPairFirstOwnerAction w j)
      (preE7NoPairNoC3CertifiedFirstOwnerPredicate FamilyAction w j b) := by
  apply fusionOrbitNatural_and
  · exact preE7NoPairNoC3FirstOwnerPredicate_natural
      (ownerOrResidualEligible
        (preE7NoPairNoC3EarlierFamilyPredicate FamilyAction))
      (ownerOrResidualEligible_natural _
        (preE7NoPairNoC3EarlierFamilyPredicate_natural FamilyAction)) w j b
  · intro _ _
    exact id

/-! ## The cover which retains a family orbit -/

/-- If an earlier family owns the subgroup, the physical cover uses an orbit
which carries that family's certificate.  Only the terminal residual branch
uses an arbitrary pre-`E7` violation orbit.  Thus the residual source really
has no family orbit whenever its later argument uses that fact. -/
theorem preE7NoPairNoC3_certifiedOwnerOrResidual_physical_cover
    (FamilyAction : PreE7NoPairNoC3EarlierOwnerFamily →
      ∀ w, PreE7NonPairActionClass w → Prop)
    (n : ℕ) (H : Subgroup (Equiv.Perm (Fin n)))
    (hH : H ∈ PreE7NoPairNoC3ResidualSubgroupSet n) :
    ∃ j : GrowingQuotientPhysicalIndex
        (ι := fun w => PreE7NonPairFirstOwnerIndex
          (preE7NoPairNoC3EarlierOwnerCount + 1) w) 3 n,
      H ∈ GrowingQuotientCanonicalFamily 3 n
        preE7NonPairFirstOwnerAction
        (preE7NoPairNoC3CertifiedFirstOwnerPredicate FamilyAction) j := by
  let Earlier := preE7NoPairNoC3EarlierFamilyPredicate FamilyAction
  obtain ⟨owner, howner⟩ := firstOwned_exists
    (ownerOrResidualEligible Earlier n) H
      (ownerOrResidualEligible_cover Earlier H)
  by_cases ho : owner.val < preE7NoPairNoC3EarlierOwnerCount
  · let k : Fin preE7NoPairNoC3EarlierOwnerCount := ⟨owner.val, ho⟩
    have howner_eq : owner = k.castSucc := by
      apply Fin.ext
      rfl
    have hearlier : Earlier n k H := by
      simpa only [howner_eq, ownerOrResidualEligible_castSucc] using howner.1
    obtain ⟨W⟩ := hearlier
    have hw : Nat.card W.orbit.orbit = W.width := by
      simpa only [Nat.card_fin] using (Nat.card_congr W.chart).symm
    have hwn : W.width ≤ n := by
      have hcard := Nat.card_le_card_of_injective
        (Subtype.val : W.orbit.orbit → Fin n) Subtype.val_injective
      simpa only [hw, Nat.card_fin] using hcard
    have hmem : W.width ∈ Finset.Ico 3 (n + 1) :=
      Finset.mem_Ico.mpr ⟨W.width_three, Nat.lt_succ_of_le hwn⟩
    let j : GrowingQuotientPhysicalIndex
        (ι := fun w => PreE7NonPairFirstOwnerIndex
          (preE7NoPairNoC3EarlierOwnerCount + 1) w) 3 n :=
      ⟨⟨W.width, hmem⟩, (owner, W.action)⟩
    refine ⟨j, ?_⟩
    have hold := mem_widthCanonicalFamily_preE7NoPairNoC3FirstOwner
      (ownerOrResidualEligible Earlier)
      (ownerOrResidualEligible_natural Earlier
        (preE7NoPairNoC3EarlierFamilyPredicate_natural FamilyAction))
      H hH.1.1.1.1 hH.2 owner howner W.orbit hw hwn W.action W.chart
        W.action_eq
    have hselected : preE7NoPairNoC3SelectedActionEligible
        FamilyAction W.width (owner, W.action) := by
      rw [howner_eq]
      exact (preE7NoPairNoC3SelectedActionEligible_castSucc
        FamilyAction k W.action).2 W.applies
    change H ∈ FusionWidthCanonicalFamily
      (preE7NonPairFirstOwnerAction W.width (owner, W.action)) _
      (preE7NoPairNoC3CertifiedFirstOwnerPredicate
        FamilyAction W.width (owner, W.action) (n - W.width))
    have hpredicate :
        preE7NoPairNoC3CertifiedFirstOwnerPredicate
            FamilyAction W.width (owner, W.action) (n - W.width) =
          preE7NoPairNoC3FirstOwnerPredicate
            (ownerOrResidualEligible Earlier) W.width
              (owner, W.action) (n - W.width) := by
      funext L
      simp only [preE7NoPairNoC3CertifiedFirstOwnerPredicate,
        hselected, and_true]
      rfl
    rw [hpredicate]
    exact hold
  · have howner_eq : owner = Fin.last preE7NoPairNoC3EarlierOwnerCount :=
      Fin.eq_last_of_not_lt ho
    obtain ⟨o, hbad⟩ := exists_preE7ViolationOrbit H hH.1.1.2
    let w : ℕ := Nat.card o.orbit
    have hw : Nat.card o.orbit = w := rfl
    let outside : OutsideOrbit H := ⟨o, hbad.1, hbad.2.1⟩
    have hw3 : 3 ≤ w := by
      have h := outsideOrbit_card_gt_two H outside
      change 2 < Nat.card o.orbit at h
      omega
    have hwn : w ≤ n := by
      have hcard := Nat.card_le_card_of_injective
        (Subtype.val : o.orbit → Fin n) Subtype.val_injective
      simpa only [hw, Nat.card_fin] using hcard
    obtain ⟨i, eO, himage⟩ := Non2TransitiveActionClass.orbit_cover
      H o hw hbad.1
    have hpre : IsPreE7ActionClass w i :=
      isPreE7ActionClass_of_violation H o hbad i eO himage
    let a : PreE7ActionClass w := ⟨i, hpre⟩
    have hfree : IsPreE7NonPairActionClass w a :=
      isPreE7NonPairActionClass_of_violation H hH.1.1.1.1 hH.1.2 o hbad
        hw hwn i eO himage
    let a' : PreE7NonPairActionClass w := ⟨a, hfree⟩
    have hmem : w ∈ Finset.Ico 3 (n + 1) :=
      Finset.mem_Ico.mpr ⟨hw3, Nat.lt_succ_of_le hwn⟩
    let j : GrowingQuotientPhysicalIndex
        (ι := fun d => PreE7NonPairFirstOwnerIndex
          (preE7NoPairNoC3EarlierOwnerCount + 1) d) 3 n :=
      ⟨⟨w, hmem⟩, (owner, a')⟩
    refine ⟨j, ?_⟩
    have hold := mem_widthCanonicalFamily_preE7NoPairNoC3FirstOwner
      (ownerOrResidualEligible Earlier)
      (ownerOrResidualEligible_natural Earlier
        (preE7NoPairNoC3EarlierFamilyPredicate_natural FamilyAction))
      H hH.1.1.1.1 hH.2 owner howner o hw hwn a' eO (by
        simpa only [a', a, preE7NonPairAction, preE7Action] using himage)
    have hselected : preE7NoPairNoC3SelectedActionEligible
        FamilyAction w (owner, a') := by
      rw [howner_eq]
      exact preE7NoPairNoC3SelectedActionEligible_last FamilyAction a'
    change H ∈ FusionWidthCanonicalFamily
      (preE7NonPairFirstOwnerAction w (owner, a')) _
      (preE7NoPairNoC3CertifiedFirstOwnerPredicate
        FamilyAction w (owner, a') (n - w))
    have hpredicate :
        preE7NoPairNoC3CertifiedFirstOwnerPredicate
            FamilyAction w (owner, a') (n - w) =
          preE7NoPairNoC3FirstOwnerPredicate
            (ownerOrResidualEligible Earlier) w (owner, a') (n - w) := by
      funext L
      simp only [preE7NoPairNoC3CertifiedFirstOwnerPredicate,
        hselected, and_true]
      rfl
    rw [hpredicate]
    exact hold

/-! ## One certificate per retained action class -/

/-- The broad source on which every historical family estimate is proved.
It contains no exclusion of other families and hence no owner-order premise. -/
def preE7NoPairNoC3BroadActionPredicate
    (w : ℕ) (i : PreE7NonPairActionClass w) (b : ℕ)
    (H : Subgroup (preE7NonPairAction w i × Equiv.Perm (Fin b))) : Prop :=
  preE7NonPairPredicate w i b H ∧
    noC3CompleteSourcePredicate (preE7NonPairAction w i) H

/-- A complete family certificate on one literal retained action class.  Its
main comparator and pure cold tail are charged together on every normal axis.
The template and exceptional-moment tags are determined by `family`; future
constructors for the five templates must produce this common conclusion. -/
structure PreE7EarlierActionComparatorCertificate
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (w : ℕ) (i : PreE7NonPairActionClass w) where
  R : Type
  [groupR : Group R]
  [finiteR : Finite R]
  v : ℕ
  action : R →* Equiv.Perm (Fin v)
  action_injective : Function.Injective action
  C : ℕ → {N : Subgroup (preE7NonPairAction w i) // N.Normal} → ℝ
  tailCoefficient :
    ℕ → {N : Subgroup (preE7NonPairAction w i) // N.Normal} → ℝ
  eta : ℝ
  delta : ℝ
  cutoff : ℝ
  alpha : ℝ
  theta : ℝ
  alpha_eq : alpha = eta + cutoff
  coefficient_nonneg : ∀ b N, 0 ≤ C b N
  tail_nonneg : ∀ b N, 0 ≤ tailCoefficient b N
  broad_axis_envelope : ∀ b N (J : Subgroup (Equiv.Perm (Fin b))),
    fusionSurvivingEpiCount (preE7NonPairAction w i)
        (preE7NoPairNoC3BroadActionPredicate w i b) N J ≤
      (C b N * (2 : ℝ) ^ (eta * b)) *
          completeQuotientWeight (R := R) J +
        tailCoefficient b N * (2 : ℝ) ^ (theta * b)

attribute [instance]
  PreE7EarlierActionComparatorCertificate.groupR
  PreE7EarlierActionComparatorCertificate.finiteR

/-- The action predicate used by the concrete catalogue: there exists a
family-specific certificate with its actual comparator and additive envelope.
No census or precedence proof is part of this predicate. -/
def preE7NoPairNoC3EarlierFamilyAction
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (w : ℕ) (i : PreE7NonPairActionClass w) : Prop :=
  Nonempty (PreE7EarlierActionComparatorCertificate family w i)

/-- The concrete 53 predicates are now actual existence-of-certificate
predicates on literal action orbits. -/
abbrev preE7NoPairNoC3EarlierPredicates :=
  preE7NoPairNoC3EarlierFamilyPredicate
    preE7NoPairNoC3EarlierFamilyAction

theorem preE7NoPairNoC3EarlierPredicates_natural :
    DegreeNaturalOwnerMenu preE7NoPairNoC3EarlierPredicates :=
  preE7NoPairNoC3EarlierFamilyPredicate_natural _

/-- The certified first-owner source is a restriction of the broad source on
which a family theorem is proved. -/
theorem preE7NoPairNoC3CertifiedFirstOwnerPredicate_implies_broad
    (w : ℕ)
    (j : PreE7NonPairFirstOwnerIndex
      (preE7NoPairNoC3EarlierOwnerCount + 1) w)
    (b : ℕ)
    (H : Subgroup
      (preE7NonPairFirstOwnerAction w j × Equiv.Perm (Fin b))) :
    preE7NoPairNoC3CertifiedFirstOwnerPredicate
        preE7NoPairNoC3EarlierFamilyAction w j b H →
      preE7NoPairNoC3BroadActionPredicate w j.2 b H := by
  rintro ⟨⟨⟨hordinary, _howner⟩, hnoC3⟩, _hselected⟩
  exact ⟨hordinary, hnoC3⟩

/-- One selected comparator envelope for a certified local cell.  Earlier
families supply this from their action certificate; the terminal residual
lane supplies the same shape from the retained-cell/Yoneda theorem. -/
structure PreE7NoPairNoC3AxisComparatorChoice
    (w : ℕ)
    (j : PreE7NonPairFirstOwnerIndex
      (preE7NoPairNoC3EarlierOwnerCount + 1) w) where
  R : Type
  [groupR : Group R]
  [finiteR : Finite R]
  v : ℕ
  action : R →* Equiv.Perm (Fin v)
  action_injective : Function.Injective action
  C : ℕ →
    {N : Subgroup (preE7NonPairFirstOwnerAction w j) // N.Normal} → ℝ
  tailCoefficient : ℕ →
    {N : Subgroup (preE7NonPairFirstOwnerAction w j) // N.Normal} → ℝ
  eta : ℝ
  delta : ℝ
  cutoff : ℝ
  alpha : ℝ
  theta : ℝ
  alpha_eq : alpha = eta + cutoff
  coefficient_nonneg : ∀ b N, 0 ≤ C b N
  tail_nonneg : ∀ b N, 0 ≤ tailCoefficient b N
  axis_envelope : ∀ b N (J : Subgroup (Equiv.Perm (Fin b))),
    fusionSurvivingEpiCount (preE7NonPairFirstOwnerAction w j)
        (preE7NoPairNoC3CertifiedFirstOwnerPredicate
          preE7NoPairNoC3EarlierFamilyAction w j b) N J ≤
      (C b N * (2 : ℝ) ^ (eta * b)) *
          completeQuotientWeight (R := R) J +
        tailCoefficient b N * (2 : ℝ) ^ (theta * b)

attribute [instance]
  PreE7NoPairNoC3AxisComparatorChoice.groupR
  PreE7NoPairNoC3AxisComparatorChoice.finiteR

namespace PreE7NoPairNoC3AxisComparatorChoice

/-- Install one actual historical-family certificate on its matching owner
and original action. -/
noncomputable def ofEarlierCertificate
    (k : Fin preE7NoPairNoC3EarlierOwnerCount)
    {w : ℕ} (U : PreE7NonPairActionClass w)
    (C₀ : PreE7EarlierActionComparatorCertificate
      (preE7NoPairNoC3EarlierOwnerEquiv k) w U) :
    PreE7NoPairNoC3AxisComparatorChoice w (k.castSucc, U) where
  R := C₀.R
  groupR := C₀.groupR
  finiteR := C₀.finiteR
  v := C₀.v
  action := C₀.action
  action_injective := C₀.action_injective
  C := C₀.C
  tailCoefficient := C₀.tailCoefficient
  eta := C₀.eta
  delta := C₀.delta
  cutoff := C₀.cutoff
  alpha := C₀.alpha
  theta := C₀.theta
  alpha_eq := C₀.alpha_eq
  coefficient_nonneg := C₀.coefficient_nonneg
  tail_nonneg := C₀.tail_nonneg
  axis_envelope := by
    intro b N J
    exact (fusionSurvivingEpiCount_mono
      (preE7NoPairNoC3CertifiedFirstOwnerPredicate_implies_broad
        w (k.castSucc, U) b) N J).trans
      (C₀.broad_axis_envelope b N J)

/-- A nonmatching earlier owner/action cell is literally empty because the
local action check is part of the predicate. -/
noncomputable def emptyEarlier
    (k : Fin preE7NoPairNoC3EarlierOwnerCount)
    {w : ℕ} (U : PreE7NonPairActionClass w)
    (hmissing : ¬ preE7NoPairNoC3EarlierFamilyAction
      (preE7NoPairNoC3EarlierOwnerEquiv k) w U) :
    PreE7NoPairNoC3AxisComparatorChoice w (k.castSucc, U) where
  R := PUnit
  v := 0
  action := 1
  action_injective := fun _ _ _ => Subsingleton.elim _ _
  C := fun _ _ => 0
  tailCoefficient := fun _ _ => 0
  eta := 0
  delta := 0
  cutoff := 0
  alpha := 0
  theta := 0
  alpha_eq := by norm_num
  coefficient_nonneg := fun _ _ => le_rfl
  tail_nonneg := fun _ _ => le_rfl
  axis_envelope := by
    intro b N J
    let F := {β : GroupEpimorphism J
        (preE7NonPairFirstOwnerAction w (k.castSucc, U) ⧸ N.1) //
      preE7NoPairNoC3CertifiedFirstOwnerPredicate
        preE7NoPairNoC3EarlierFamilyAction w (k.castSucc, U) b
          (fusionFullGoursatEncode N J β).1}
    letI : IsEmpty F := ⟨fun β => hmissing
      ((preE7NoPairNoC3SelectedActionEligible_castSucc
        preE7NoPairNoC3EarlierFamilyAction k U).mp β.2.2)⟩
    unfold fusionSurvivingEpiCount
    change (Nat.card F : ℝ) ≤ _
    rw [Nat.card_eq_zero.mpr (Or.inl inferInstance)]
    norm_num

end PreE7NoPairNoC3AxisComparatorChoice

/-- Select the real family certificate when the owner and displayed action
match; use the empty cell otherwise; and delegate only the final owner to the
retained residual construction. -/
noncomputable def preE7NoPairNoC3AxisComparatorChoice
    (Residual : ∀ w (U : PreE7NonPairActionClass w),
      PreE7NoPairNoC3AxisComparatorChoice w
        (Fin.last preE7NoPairNoC3EarlierOwnerCount, U))
    (w : ℕ)
    (owner : Fin (preE7NoPairNoC3EarlierOwnerCount + 1))
    (U : PreE7NonPairActionClass w) :
    PreE7NoPairNoC3AxisComparatorChoice w (owner, U) := by
  classical
  by_cases ho : owner.val < preE7NoPairNoC3EarlierOwnerCount
  · let k : Fin preE7NoPairNoC3EarlierOwnerCount := ⟨owner.val, ho⟩
    have howner : owner = k.castSucc := by
      apply Fin.ext
      rfl
    by_cases hC : preE7NoPairNoC3EarlierFamilyAction
        (preE7NoPairNoC3EarlierOwnerEquiv k) w U
    · simpa only [howner] using
        (PreE7NoPairNoC3AxisComparatorChoice.ofEarlierCertificate
          k U (Classical.choice hC))
    · simpa only [howner] using
        (PreE7NoPairNoC3AxisComparatorChoice.emptyEarlier k U hC)
  · have howner : owner = Fin.last preE7NoPairNoC3EarlierOwnerCount :=
      Fin.eq_last_of_not_lt ho
    simpa only [howner] using Residual w U

/-- Assemble the actual earlier-family catalogue and any independently proved
terminal retained-cell envelope into the cover-parametric additive interface.
This is the replacement for the obsolete all-multiplicative core export. -/
noncomputable def preE7NoPairNoC3_localAdditiveAxisData_of_residual
    (Residual : ∀ w (U : PreE7NonPairActionClass w),
      PreE7NoPairNoC3AxisComparatorChoice w
        (Fin.last preE7NoPairNoC3EarlierOwnerCount, U)) :
    PreE7NoPairNoC3LocalAdditiveAxisData
      preE7NoPairNoC3EarlierOwnerCount where
  P := preE7NoPairNoC3CertifiedFirstOwnerPredicate
    preE7NoPairNoC3EarlierFamilyAction
  P_natural := preE7NoPairNoC3CertifiedFirstOwnerPredicate_natural _
  physical_cover :=
    preE7NoPairNoC3_certifiedOwnerOrResidual_physical_cover _
  R := fun w j =>
    (preE7NoPairNoC3AxisComparatorChoice Residual w j.1 j.2).R
  groupR := fun w j =>
    (preE7NoPairNoC3AxisComparatorChoice Residual w j.1 j.2).groupR
  finiteR := fun w j =>
    (preE7NoPairNoC3AxisComparatorChoice Residual w j.1 j.2).finiteR
  C := fun w j =>
    (preE7NoPairNoC3AxisComparatorChoice Residual w j.1 j.2).C
  tailCoefficient := fun w j =>
    (preE7NoPairNoC3AxisComparatorChoice Residual w j.1 j.2).tailCoefficient
  v := fun w j =>
    (preE7NoPairNoC3AxisComparatorChoice Residual w j.1 j.2).v
  eta := fun w j =>
    (preE7NoPairNoC3AxisComparatorChoice Residual w j.1 j.2).eta
  delta := fun w j =>
    (preE7NoPairNoC3AxisComparatorChoice Residual w j.1 j.2).delta
  cutoff := fun w j =>
    (preE7NoPairNoC3AxisComparatorChoice Residual w j.1 j.2).cutoff
  alpha := fun w j =>
    (preE7NoPairNoC3AxisComparatorChoice Residual w j.1 j.2).alpha
  theta := fun w j =>
    (preE7NoPairNoC3AxisComparatorChoice Residual w j.1 j.2).theta
  action := fun w j =>
    (preE7NoPairNoC3AxisComparatorChoice Residual w j.1 j.2).action
  action_injective := fun w j =>
    (preE7NoPairNoC3AxisComparatorChoice Residual w j.1 j.2).action_injective
  coefficient_nonneg := fun w j =>
    (preE7NoPairNoC3AxisComparatorChoice Residual w j.1 j.2).coefficient_nonneg
  tail_nonneg := fun w j =>
    (preE7NoPairNoC3AxisComparatorChoice Residual w j.1 j.2).tail_nonneg
  alpha_eq := fun w j =>
    (preE7NoPairNoC3AxisComparatorChoice Residual w j.1 j.2).alpha_eq
  axis_envelope := fun w j =>
    (preE7NoPairNoC3AxisComparatorChoice Residual w j.1 j.2).axis_envelope

/-- Forgetting the no-regular-`C3` conjunct recovers the broader non-pair
first-owner predicate. -/
theorem preE7NoPairNoC3FirstOwnerPredicate_implies_nonPair
    {r w b : ℕ}
    (Earlier : ∀ d, Fin r → Subgroup (Equiv.Perm (Fin d)) → Prop)
    (i : PreE7NonPairFirstOwnerIndex r w)
    (H : Subgroup
      (preE7NonPairFirstOwnerAction w i × Equiv.Perm (Fin b))) :
    preE7NoPairNoC3FirstOwnerPredicate Earlier w i b H →
      preE7NonPairFirstOwnerPredicate Earlier w i b H :=
  fun h => h.1

/-- Every direct envelope for the broad non-pair source restricts to the
no-pair/no-`C3` source with coefficient one and the same complete quotient
weight. -/
theorem preE7NoPairNoC3_ownedEnvelope_of_nonPair
    {r w b : ℕ}
    (Earlier : ∀ d, Fin r → Subgroup (Equiv.Perm (Fin d)) → Prop)
    (i : PreE7NonPairFirstOwnerIndex r w)
    (N : {N : Subgroup (preE7NonPairFirstOwnerAction w i) // N.Normal})
    {R : Type*} [Group R] [Finite R]
    (h : ∀ J : Subgroup (Equiv.Perm (Fin b)),
      fusionSurvivingEpiCount (preE7NonPairFirstOwnerAction w i)
          (preE7NonPairFirstOwnerPredicate Earlier w i b) N J ≤
        completeQuotientWeight (R := R) J)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount (preE7NonPairFirstOwnerAction w i)
        (preE7NoPairNoC3FirstOwnerPredicate Earlier w i b) N J ≤
      completeQuotientWeight (R := R) J :=
  (fusionSurvivingEpiCount_mono
    (preE7NoPairNoC3FirstOwnerPredicate_implies_nonPair Earlier i)
    N J).trans (h J)

/-- Structural restriction of an already checked broad non-pair owner datum.
The actual earlier-owner predicates are unchanged; only their complete-source
domain is narrowed by the no-regular-`C3` conjunct. -/
noncomputable def PreE7NoPairNoC3EarlierComparatorCore.ofNonPairOwnerData
    {r : ℕ} (D : PreE7NonPairOwnerComparatorData r) :
    PreE7NoPairNoC3EarlierComparatorCore r where
  Earlier := D.Earlier
  earlier_natural := D.earlier_natural
  R := D.R
  groupR := D.groupR
  finiteR := D.finiteR
  Owned := D.Owned
  v := D.v
  action := D.action
  action_injective := D.action_injective
  owned_envelope := by
    intro w i b N hN J
    exact preE7NoPairNoC3_ownedEnvelope_of_nonPair
      (ownerOrResidualEligible D.Earlier) i N
      (D.owned_envelope w i b N hN) J

/-- Numerical decoration transported unchanged from the broad non-pair datum
to its narrowed structural core. -/
noncomputable def PreE7NoPairNoC3OwnerNumerics.ofNonPairOwnerData
    {r : ℕ} (D : PreE7NonPairOwnerComparatorData r) :
    PreE7NoPairNoC3OwnerNumerics
      (PreE7NoPairNoC3EarlierComparatorCore.ofNonPairOwnerData D) where
  C := D.C
  eta := D.eta
  delta := D.delta
  cutoff := D.cutoff
  alpha := D.alpha
  coefficient_nonneg := D.coefficient_nonneg
  alpha_eq := D.alpha_eq

/-- Complete restriction of a broad non-pair owner datum.  This is the
canonical route by which the actual 53-family catalogue, once constructed on
its original source, enters the final no-pair/no-`C3` frontier. -/
noncomputable def PreE7NonPairOwnerComparatorData.restrictNoC3
    {r : ℕ} (D : PreE7NonPairOwnerComparatorData r) :
    PreE7NoPairNoC3OwnerData r :=
  (PreE7NoPairNoC3EarlierComparatorCore.ofNonPairOwnerData D).withNumerics
    (PreE7NoPairNoC3OwnerNumerics.ofNonPairOwnerData D)

@[simp] theorem PreE7NonPairOwnerComparatorData.restrictNoC3_Earlier
    {r : ℕ} (D : PreE7NonPairOwnerComparatorData r) :
    D.restrictNoC3.Earlier = D.Earlier := rfl

@[simp] theorem PreE7NonPairOwnerComparatorData.restrictNoC3_Owned
    {r : ℕ} (D : PreE7NonPairOwnerComparatorData r) :
    D.restrictNoC3.Owned = D.Owned := rfl

@[simp] theorem PreE7NonPairOwnerComparatorData.restrictNoC3_C
    {r : ℕ} (D : PreE7NonPairOwnerComparatorData r) :
    D.restrictNoC3.C = D.C := rfl

@[simp] theorem PreE7NonPairOwnerComparatorData.restrictNoC3_parameters
    {r : ℕ} (D : PreE7NonPairOwnerComparatorData r) :
    D.restrictNoC3.v = D.v ∧
      D.restrictNoC3.eta = D.eta ∧
      D.restrictNoC3.delta = D.delta ∧
      D.restrictNoC3.cutoff = D.cutoff ∧
      D.restrictNoC3.alpha = D.alpha := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
