import SymmetricSubgroupAsymptotics.FiniteNormalJoinWordRegistry
import SymmetricSubgroupAsymptotics.Non2PreE7RankTailSourceDichotomyClosure
import SymmetricSubgroupAsymptotics.ZmudFaithfulCharacterInput
import Mathlib.Tactic.FinCases

/-!
# Finite normal-state importer for the remaining degree-two pair catalogues

The degree-six emitter already uses a checked conjugacy cover and a join
state machine to prove that its finite list exhausts the literal normal
subgroups.  The degree-six dispatcher, however, is tied to twelve points and
to the special B6 quotient certificate.  The nonbinary degree-sixteen and
pair-top degree-twelve/sixteen datasets need the same finite-normal bridge at
different widths and with the ordinary character templates.

This file supplies that common semantic target.  An exporter provides a
finite normal-state registry, one quotient payload on every state, and
finite sums of the two template coefficients.  The importer proves that the
state list is equivalent to the type of all literal normal subgroups and
therefore transports both the dependent quotient payloads and their sums.
No completeness bit from a JSON file is trusted.

`FiniteNormalStateRegistry.ofWordRegistry` is the intended input path for
`nonbinary_normals.jsonl.gz` and `pair_top_groups.jsonl.gz`: normality and
surjectivity come from the already checked conjugacy/join-word machinery.
Only state distinctness remains an emitter-side finite check.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

universe u

/-! ## A width-independent complete finite normal registry -/

/-- A finite, duplicate-free enumeration of all literal normal subgroups of
one finite group.  The `complete` field is normally supplied by
`FiniteNormalJoinRegistry.complete`, rather than by a producer assertion. -/
structure FiniteNormalStateRegistry (U : Type) [Group U] [Finite U] : Type 1 where
  State : Type
  [state_finite : Finite State]
  state : State → Subgroup U
  state_normal : ∀ i, (state i).Normal
  state_injective : Function.Injective state
  complete : ∀ N : Subgroup U, [N.Normal] → ∃ i, state i = N

attribute [instance] FiniteNormalStateRegistry.state_finite

namespace FiniteNormalStateRegistry

variable {U : Type} [Group U] [Finite U]
  (R : FiniteNormalStateRegistry U)

/-- The type of literal normal axes of a finite group is
finite.  This noncomputable instance supports semantic pilot registries and
the few uniform natural groups for which no compressed word table is
needed. -/
noncomputable instance normalAxesFinite :
    Finite {N : Subgroup U // N.Normal} :=
  Finite.of_injective
    (fun N : {N : Subgroup U // N.Normal} => (N.1 : Set U)) (by
      intro A B h
      exact Subtype.ext (SetLike.coe_injective h))

/-- Canonical census-free registry of all literal normal subgroups.  This
does not assert a producer list is complete: its states are the normal axes
themselves. -/
noncomputable def allNormals : FiniteNormalStateRegistry U where
  State := {N : Subgroup U // N.Normal}
  state := Subtype.val
  state_normal := Subtype.property
  state_injective := Subtype.val_injective
  complete N := ⟨⟨N, inferInstance⟩, rfl⟩

/-- A state viewed as a literal normal axis. -/
def normalAxis (i : R.State) : {N : Subgroup U // N.Normal} :=
  ⟨R.state i, R.state_normal i⟩

theorem normalAxis_injective : Function.Injective R.normalAxis := by
  intro i j hij
  apply R.state_injective
  exact congrArg Subtype.val hij

theorem normalAxis_surjective : Function.Surjective R.normalAxis := by
  intro N
  letI : N.1.Normal := N.2
  obtain ⟨i, hi⟩ := R.complete N.1
  exact ⟨i, Subtype.ext hi⟩

/-- The checked finite states are exactly the literal normal axes. -/
noncomputable def normalAxisEquiv :
    R.State ≃ {N : Subgroup U // N.Normal} :=
  Equiv.ofBijective R.normalAxis
    ⟨R.normalAxis_injective, R.normalAxis_surjective⟩

/-- Reindex an arbitrary literal normal-axis sum by the checked states. -/
theorem fusionAxisEnvelopeTotal_eq_stateSum
    {w : ℕ} {V : Subgroup (Equiv.Perm (Fin w))}
    (S : FiniteNormalStateRegistry V)
    (C : {N : Subgroup V // N.Normal} → ℝ) :
    fusionAxisEnvelopeTotal V C = ∑ i : S.State, C (S.normalAxis i) := by
  unfold fusionAxisEnvelopeTotal
  exact (Fintype.sum_equiv S.normalAxisEquiv
    (fun i : S.State => C (S.normalAxis i)) C (fun _ => rfl)).symm

/-- Build the semantic registry from the existing conjugacy-cover and
normal-join-word certificates.  This constructor is independent of the
permutation width and is shared by the degree-16 nonbinary data and the
count-12/count-16 pair-top data. -/
noncomputable def ofWordRegistry
    {I ι κ : Type} [Finite I]
    {c : ℕ} {representative : Fin c → U}
    (C : FiniteConjugacyCardinalCover representative)
    (ambient : ι → U) (stateGenerators : I → κ → U)
    (D : FiniteNormalJoinWordRegistryData C ambient stateGenerators)
    (hinjective : Function.Injective
      (fun i => Subgroup.closure (Set.range (stateGenerators i)))) :
    FiniteNormalStateRegistry U where
  State := I
  state i := Subgroup.closure (Set.range (stateGenerators i))
  state_normal i := D.toRegistry.normal i
  state_injective := hinjective
  complete N := D.complete N

/-- Duplicate-safe form of `ofWordRegistry`.  Its state type is the finite
range of the generated subgroup map, so no separate pairwise-distinctness
certificate is needed.  This is useful when an older complete word registry
was generated before the importer required canonical state indices. -/
noncomputable def ofWordRegistryRange
    {I ι κ : Type} [Finite I]
    {c : ℕ} {representative : Fin c → U}
    (C : FiniteConjugacyCardinalCover representative)
    (ambient : ι → U) (stateGenerators : I → κ → U)
    (D : FiniteNormalJoinWordRegistryData C ambient stateGenerators) :
    FiniteNormalStateRegistry U := by
  let rawState : I → Subgroup U := fun i =>
    Subgroup.closure (Set.range (stateGenerators i))
  let State := Set.range rawState
  let enumerate : I → State := fun i => ⟨rawState i, ⟨i, rfl⟩⟩
  letI : Finite State := Finite.of_surjective enumerate (by
    rintro ⟨_, i, rfl⟩
    exact ⟨i, rfl⟩)
  exact
    { State := State
      state := Subtype.val
      state_normal := by
        rintro ⟨_, i, rfl⟩
        exact (D.normality i).normal D.ambient_full
      state_injective := Subtype.val_injective
      complete := by
        intro N _
        obtain ⟨i, hi⟩ := D.complete N
        exact ⟨enumerate i, hi⟩ }

/-- Transport a complete word registry from its executable finite Cayley
group to the literal permutation subgroup used by a catalogue row.  The
finite range again removes any need to re-prove that old generated state
indices were duplicate-free. -/
noncomputable def ofWordRegistryEquiv
    {G I ι κ : Type} [Group G] [Finite G] [Finite I]
    {c : ℕ} {representative : Fin c → G}
    (C : FiniteConjugacyCardinalCover representative)
    (ambient : ι → G) (stateGenerators : I → κ → G)
    (D : FiniteNormalJoinWordRegistryData C ambient stateGenerators)
    (e : G ≃* U) : FiniteNormalStateRegistry U := by
  let rawState : I → Subgroup U := fun i =>
    (Subgroup.closure (Set.range (stateGenerators i))).map e.toMonoidHom
  let State := Set.range rawState
  let enumerate : I → State := fun i => ⟨rawState i, ⟨i, rfl⟩⟩
  letI : Finite State := Finite.of_surjective enumerate (by
    rintro ⟨_, i, rfl⟩
    exact ⟨i, rfl⟩)
  exact
    { State := State
      state := Subtype.val
      state_normal := by
        rintro ⟨_, i, rfl⟩
        letI : (Subgroup.closure
            (Set.range (stateGenerators i))).Normal :=
          (D.normality i).normal D.ambient_full
        exact Subgroup.Normal.map inferInstance _ e.surjective
      state_injective := Subtype.val_injective
      complete := by
        intro N _
        let M : Subgroup G := N.comap e.toMonoidHom
        letI : M.Normal := Subgroup.Normal.comap inferInstance e.toMonoidHom
        obtain ⟨i, hi⟩ := D.complete M
        refine ⟨enumerate i, ?_⟩
        change (Subgroup.closure
          (Set.range (stateGenerators i))).map e.toMonoidHom = N
        rw [hi]
        exact Subgroup.map_comap_eq_self_of_surjective e.surjective N }

end FiniteNormalStateRegistry

/-! ## Dependent payload dispatch -/

/-- A dependent payload recorded only on the checked finite normal states. -/
structure FiniteNormalStateFamily
    {U : Type} [Group U] [Finite U]
    (R : FiniteNormalStateRegistry U)
    (Payload : {N : Subgroup U // N.Normal} → Type u) : Type (max 1 u) where
  state : ∀ i : R.State, Payload (R.normalAxis i)

namespace FiniteNormalStateFamily

variable {U : Type} [Group U] [Finite U]
  {R : FiniteNormalStateRegistry U}
  {Payload : {N : Subgroup U // N.Normal} → Type u}
  (F : FiniteNormalStateFamily R Payload)

/-- Transport the payload at the inverse finite state to an arbitrary
literal normal subgroup. -/
noncomputable def dispatch
    (N : {N : Subgroup U // N.Normal}) : Payload N :=
  cast (congrArg Payload (R.normalAxisEquiv.apply_symm_apply N))
    (F.state (R.normalAxisEquiv.symm N))

end FiniteNormalStateFamily

/-! ## Mixed-character rows -/

/-- The semantic certificate required on one proper normal state of a
mixed-character row.  This is the precise Lean meaning of a JSON `mixed`
axis: the tuple is an actual jointly faithful character tuple, its mode is
mixed, and its exact slope lies in the pre-E7 window. -/
abbrev PreE7FiniteMixedCharacterAxis
    {w : ℕ} (U : Subgroup (Equiv.Perm (Fin w)))
    (N : {N : Subgroup U // N.Normal}) :=
  N.1 ≠ ⊤ →
    {c : CharacterQuotientCertificate (U ⨸ N.1) //
      c.IsBinaryMixed ∧ c.slope ≤ preE7CharacterWindow w}

/-- Compact structural input for the mixed tuples stored in the finite
datasets.  The displayed linear characters cut the quotient down to
`generalKernel`; Zmud is then applied only to that quotient.  Thus an
exporter records homomorphisms, one normal subgroup, a socle generator
tuple, and the literal kernel-intersection equality.  It does not need to
emit matrices for complex irreducible representations. -/
structure PreE7LinearZmudTupleData (Q : Type) [Group Q] : Type 1 where
  linearCount : ℕ
  generalCount : ℕ
  linear : Fin linearCount → Q →* ℂˣ
  generalKernel : Subgroup Q
  [generalKernel_normal : generalKernel.Normal]
  generalSocleGenerator :
    SocleNormalGeneratorBound (Q ⨸ generalKernel) generalCount
  kernel_inf : (⨅ j, (linear j).ker) ⊓ generalKernel = ⊥

attribute [instance] PreE7LinearZmudTupleData.generalKernel_normal

namespace PreE7LinearZmudTupleData

variable {Q : Type} [Group Q] [Finite Q]
  (D : PreE7LinearZmudTupleData Q)

noncomputable def generalFamily
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    Fin D.generalCount →
      FiniteIrreducibleRepresentation ℂ (Q ⨸ D.generalKernel) :=
  Classical.choose
    (hZmud (Q ⨸ D.generalKernel) D.generalCount
      D.generalSocleGenerator)

theorem generalFamily_faithful
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    ∀ q : Q ⨸ D.generalKernel,
      (∀ j, (D.generalFamily hZmud j).action q = 1) → q = 1 :=
  Classical.choose_spec
    (hZmud (Q ⨸ D.generalKernel) D.generalCount
      D.generalSocleGenerator)

/-- Inflate one Zmud constituent from the quotient by the common general
kernel. -/
noncomputable def inflatedGeneral
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (j : Fin D.generalCount) : FiniteIrreducibleRepresentation ℂ Q := by
  let ρ := D.generalFamily hZmud j
  exact
    { Space := ρ.Space
      addCommGroup := inferInstance
      module := inferInstance
      finiteDimensional := inferInstance
      action := ρ.action.comp (QuotientGroup.mk' D.generalKernel)
      irreducible := representation_irreducible_comp ρ.action
        (QuotientGroup.mk' D.generalKernel)
        (QuotientGroup.mk'_surjective D.generalKernel) }

/-- The structural kernel equality gives the jointly faithful tuple needed
by the character envelope. -/
noncomputable def tuple
    (hZmud : ZmudFaithfulCharacterTupleInput) : CharacterSlotTuple Q where
  binaryCount := 0
  linearCount := D.linearCount
  generalCount := D.generalCount
  binary := Fin.elim0
  binary_twoGroup := fun j => Fin.elim0 j
  linear := D.linear
  general := D.inflatedGeneral hZmud
  faithful := by
    intro q _ hlinear hgeneral
    have hquot : QuotientGroup.mk' D.generalKernel q = 1 := by
      apply D.generalFamily_faithful hZmud
      intro j
      simpa only [inflatedGeneral, MonoidHom.comp_apply] using hgeneral j
    have hlin : q ∈ ⨅ j, (D.linear j).ker := by
      rw [Subgroup.mem_iInf]
      intro j
      exact (MonoidHom.mem_ker).2 (hlinear j)
    have hK : q ∈ D.generalKernel :=
      (QuotientGroup.eq_one_iff q).mp hquot
    have hbot : q ∈ (⨅ j, (D.linear j).ker) ⊓ D.generalKernel :=
      ⟨hlin, hK⟩
    rw [D.kernel_inf] at hbot
    simpa only [Subgroup.mem_bot] using hbot

noncomputable def certificate
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    CharacterQuotientCertificate Q where
  mode := .mixed
  tuple := D.tuple hZmud
  prime := 2
  known := by
    intro h
    cases h

@[simp] theorem certificate_mode
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    (D.certificate hZmud).mode = .mixed := rfl

@[simp] theorem certificate_binaryCount
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    (D.certificate hZmud).tuple.binaryCount = 0 := rfl

@[simp] theorem certificate_linearCount
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    (D.certificate hZmud).tuple.linearCount = D.linearCount := rfl

@[simp] theorem certificate_generalCount
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    (D.certificate hZmud).tuple.generalCount = D.generalCount := rfl

/-- The slope of the generated mixed certificate depends only on the two
finite slot counts.  In particular, a selected finite exporter never has to
serialize the irreducible representations supplied by Zmud's theorem. -/
@[simp] theorem certificate_slope
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    (D.certificate hZmud).slope =
      (D.linearCount : ℝ) * (Real.logb 2 3 / 3) +
        (D.generalCount : ℝ) * (Real.logb 2 5 / 3) := by
  simp only [certificate, CharacterQuotientCertificate.slope,
    certificate_binaryCount, certificate_linearCount,
    certificate_generalCount, CharacterQuotientMode.generalSlope,
    Nat.cast_zero, zero_mul, zero_add]

/-- Install one structural tuple as a finite mixed-axis payload.  The only
remaining analytic check is its explicit slope inequality. -/
noncomputable def toFiniteMixedAxis
    {w : ℕ} {U : Subgroup (Equiv.Perm (Fin w))}
    {N : {N : Subgroup U // N.Normal}}
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (hcapacity : (D.certificate hZmud).slope ≤ preE7CharacterWindow w) :
    PreE7FiniteMixedCharacterAxis U N :=
  fun _ => ⟨D.certificate hZmud, rfl, hcapacity⟩

end PreE7LinearZmudTupleData

/-- Finite normal-state data for one whole-source BCHAR row.  The proper
normal axes are semantic character certificates; the top axis is supplied
by `CharacterIntervalComparator.whole`. -/
structure PreE7FiniteMixedCharacterAxes
    (w : ℕ) (i : PreE7NonPairActionClass w) : Type 1 where
  width_lower : 8 ≤ w
  width_upper : w ≤ 12288
  registry : FiniteNormalStateRegistry (preE7NonPairAction w i)
  axes : FiniteNormalStateFamily registry
    (PreE7FiniteMixedCharacterAxis (preE7NonPairAction w i))

namespace PreE7FiniteMixedCharacterAxes

variable {w : ℕ} {i : PreE7NonPairActionClass w}
  (D : PreE7FiniteMixedCharacterAxes w i)

/-- Install the finite state certificates on every literal normal quotient. -/
noncomputable def wholeSource : CharacterWholeMenuSource w i
    CharacterQuotientCertificate.IsBinaryMixed where
  width_lower := D.width_lower
  width_upper := D.width_upper
  quotient N h := ((D.axes.dispatch N) h).1
  permitted N h := ((D.axes.dispatch N) h).2.1
  capacity N h := ((D.axes.dispatch N) h).2.2

/-- The exact character template whose coefficient sums are checked by the
finite exporter. -/
noncomputable def template : PreE7CharacterTemplateData w i :=
  D.wholeSource.toTemplateData

end PreE7FiniteMixedCharacterAxes

/-- Numerically complete finite mixed row.  Both global coefficient bounds
are finite sums over emitted states, rather than assertions quantified over
arbitrary normal subgroups. -/
structure PreE7FiniteMixedCharacterMenuData
    (w : ℕ) (i : PreE7NonPairActionClass w) : Type 1 where
  axes : PreE7FiniteMixedCharacterAxes w i
  main_state_total_bound : ∀ b,
    (∑ j : axes.registry.State,
      axes.template.mainCoefficient (axes.registry.normalAxis j)) ≤
        (2 : ℝ) ^
          (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)
  tail_state_total_bound : ∀ b,
    (∑ j : axes.registry.State,
      axes.template.tailCoefficient (axes.registry.normalAxis j)) ≤
        (2 : ℝ) ^
          (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)

namespace PreE7FiniteMixedCharacterMenuData

variable {w : ℕ} {i : PreE7NonPairActionClass w}
  (D : PreE7FiniteMixedCharacterMenuData w i)

/-- Convert the checked state sums into the literal-axis totals required by
the ordinary character menu. -/
noncomputable def menuData :
    PreE7CharacterMenuSourceData .bchar (by rfl) w i where
  source := D.axes.wholeSource
  main_total_bound b := by
    rw [D.axes.registry.fusionAxisEnvelopeTotal_eq_stateSum]
    exact D.main_state_total_bound b
  tail_total_bound b := by
    rw [D.axes.registry.fusionAxisEnvelopeTotal_eq_stateSum]
    exact D.tail_state_total_bound b

/-- A complete finite mixed row is already a concrete source at the final
rank-tail boundary. -/
noncomputable def rankTailSource :
    PreE7RankTailSourceOrYonedaTopData w i :=
  .inl (.ordinary .bchar (.character (by rfl) D.menuData))

end PreE7FiniteMixedCharacterMenuData

/-! ## Quotient-comparator rows -/

/-- The semantic character payload below the distinguished comparator
normal subgroup of a QCHAR row. -/
abbrev PreE7FiniteQcharAxis
    {w : ℕ} (U : Subgroup (Equiv.Perm (Fin w)))
    (E : Subgroup U) (N : {N : Subgroup U // N.Normal}) :=
  ¬ E ≤ N.1 →
    {c : CharacterQuotientCertificate (U ⨸ N.1) //
      c.IsLinearMixed ∧ c.slope ≤ preE7CharacterWindow w}

/-- Finite-state form of the two degree-sixteen comparator rows.  The
interval above `E` is handled by the faithful action of `U/E`; only states
strictly outside that interval carry character tuples. -/
structure PreE7FiniteQcharAxes
    (w : ℕ) (i : PreE7NonPairActionClass w) : Type 1 where
  width_lower : 8 ≤ w
  width_upper : w ≤ 12288
  registry : FiniteNormalStateRegistry (preE7NonPairAction w i)
  E : Subgroup (preE7NonPairAction w i)
  [E_normal : E.Normal]
  degree : ℕ
  action : preE7NonPairAction w i ⨸ E →* Equiv.Perm (Fin degree)
  action_injective : Function.Injective action
  degree_window : preE7CharacterRho * w ≤
    ((evenWidth w : ℝ) - ((max 2 degree : ℕ) : ℝ)) / 8
  axes : FiniteNormalStateFamily registry
    (PreE7FiniteQcharAxis (preE7NonPairAction w i) E)

attribute [instance] PreE7FiniteQcharAxes.E_normal

namespace PreE7FiniteQcharAxes

variable {w : ℕ} {i : PreE7NonPairActionClass w}
  (D : PreE7FiniteQcharAxes w i)

/-- Install the finite comparator and the state-indexed character rows in
the ordinary QCHAR source. -/
noncomputable def qcharSource : QcharSource w i where
  width_lower := D.width_lower
  width_upper := D.width_upper
  E := D.E
  degree := D.degree
  action := D.action
  action_injective := D.action_injective
  degree_window := D.degree_window
  quotient N h := ((D.axes.dispatch N) h).1
  permitted N h := ((D.axes.dispatch N) h).2.1
  capacity N h := ((D.axes.dispatch N) h).2.2

noncomputable def template : PreE7CharacterTemplateData w i :=
  D.qcharSource.toTemplateData

end PreE7FiniteQcharAxes

/-! ## Compact selected QCHAR packages -/

/-- The faithful complex-unit sign of the two-element group. -/
def binaryComplexUnitSign : Multiplicative (ZMod 2) →* ℂˣ where
  toFun x := if x.toAdd = 0 then 1 else -1
  map_one' := by simp
  map_mul' x y := by
    change (if x.toAdd + y.toAdd = 0 then (1 : ℂˣ) else -1) =
      (if x.toAdd = 0 then 1 else -1) *
        (if y.toAdd = 0 then 1 else -1)
    have hx : x.toAdd = 0 ∨ x.toAdd = 1 := by
      generalize x.toAdd = z
      fin_cases z <;> simp
    have hy : y.toAdd = 0 ∨ y.toAdd = 1 := by
      generalize y.toAdd = z
      fin_cases z <;> simp
    have htwo : (1 : ZMod 2) + 1 = 0 := by decide
    rcases hx with hx | hx <;> rcases hy with hy | hy <;>
      simp [hx, hy, htwo]

@[simp] theorem binaryComplexUnitSign_eq_one
    (x : Multiplicative (ZMod 2)) :
    binaryComplexUnitSign x = 1 ↔ x = 1 := by
  change (if x.toAdd = 0 then (1 : ℂˣ) else -1) = 1 ↔ x = 1
  by_cases h : x.toAdd = 0
  · have hx : x = 1 := Multiplicative.toAdd.injective h
    simp [hx]
  · have hx : x ≠ 1 := fun he ↦ h (congrArg Multiplicative.toAdd he)
    simp [h, hx]

/-- Finite structural form of a linear/Zmud tuple when all selected linear
characters have binary image.  An emitter only records homomorphisms into
the two-element group; the common converter supplies their complex signs. -/
structure PreE7BinaryLinearZmudTupleData
    (Q : Type) [Group Q] : Type 1 where
  linearCount : ℕ
  generalCount : ℕ
  linear : Fin linearCount → Q →* Multiplicative (ZMod 2)
  generalKernel : Subgroup Q
  [generalKernel_normal : generalKernel.Normal]
  generalSocleGenerator :
    SocleNormalGeneratorBound (Q ⨸ generalKernel) generalCount
  kernel_inf : (⨅ j, (linear j).ker) ⊓ generalKernel = ⊥

attribute [instance] PreE7BinaryLinearZmudTupleData.generalKernel_normal

namespace PreE7BinaryLinearZmudTupleData

variable {Q : Type} [Group Q]
  (D : PreE7BinaryLinearZmudTupleData Q)

/-- Interpret every retained binary homomorphism as its complex sign. -/
noncomputable def toLinearZmud : PreE7LinearZmudTupleData Q where
  linearCount := D.linearCount
  generalCount := D.generalCount
  linear j := binaryComplexUnitSign.comp (D.linear j)
  generalKernel := D.generalKernel
  generalSocleGenerator := D.generalSocleGenerator
  kernel_inf := by
    have hker : ∀ j,
        (binaryComplexUnitSign.comp (D.linear j)).ker =
          (D.linear j).ker := by
      intro j
      ext q
      simp only [MonoidHom.mem_ker, MonoidHom.comp_apply,
        binaryComplexUnitSign_eq_one]
    simp only [hker]
    exact D.kernel_inf

end PreE7BinaryLinearZmudTupleData

/-- Structural finite data for a QCHAR row before applying the published
Zmud theorem.  The selected exporter supplies one linear/Zmud tuple on each
checked normal state outside the comparator interval.  The converter below
dispatches those finitely many tuples to every literal normal quotient.

This is the intended serialization boundary for the eight degree-two
count-twelve ternary rows: it contains finite homomorphisms, subgroup data,
and socle generators, but no emitted complex representations. -/
structure PreE7FiniteQcharZmudAxes
    (w : ℕ) (i : PreE7NonPairActionClass w) : Type 1 where
  width_lower : 8 ≤ w
  width_upper : w ≤ 12288
  registry : FiniteNormalStateRegistry (preE7NonPairAction w i)
  E : Subgroup (preE7NonPairAction w i)
  [E_normal : E.Normal]
  degree : ℕ
  action : preE7NonPairAction w i ⨸ E →* Equiv.Perm (Fin degree)
  action_injective : Function.Injective action
  degree_window : preE7CharacterRho * w ≤
    ((evenWidth w : ℝ) - ((max 2 degree : ℕ) : ℝ)) / 8
  state : ∀ j : registry.State, ¬ E ≤ (registry.normalAxis j).1 →
    PreE7BinaryLinearZmudTupleData
      (preE7NonPairAction w i ⨸ (registry.normalAxis j).1)
  state_capacity : ∀ j h,
    ((state j h).linearCount : ℝ) * (Real.logb 2 3 / 3) +
        ((state j h).generalCount : ℝ) * (Real.logb 2 5 / 3) ≤
      preE7CharacterWindow w

attribute [instance] PreE7FiniteQcharZmudAxes.E_normal

namespace PreE7FiniteQcharZmudAxes

variable {w : ℕ} {i : PreE7NonPairActionClass w}
  (D : PreE7FiniteQcharZmudAxes w i)

/-- The selected quotient comparator before character tuples are installed. -/
noncomputable def interval :
    CharacterIntervalComparator (preE7NonPairAction w i) :=
  CharacterIntervalComparator.ofQuotientAction D.degree D.action
    D.action_injective

/-- The hot coefficient on one retained normal state.  It is independent of
the later choice of Zmud representations. -/
noncomputable def mainCoefficient (j : D.registry.State) : ℝ :=
  if D.E ≤ D.registry.state j then D.interval.coefficient else 0

/-- The cold coefficient on one retained normal state.  It too is determined
before applying Zmud. -/
noncomputable def tailCoefficient (j : D.registry.State) : ℝ :=
  if D.E ≤ (D.registry.normalAxis j).1 then D.interval.tail
  else (Nat.card
    ((preE7NonPairAction w i ⨸ (D.registry.normalAxis j).1) ≃*
      (preE7NonPairAction w i ⨸ (D.registry.normalAxis j).1)) : ℝ)

/-- Apply Zmud only after the selected finite state has been fixed. -/
noncomputable def toAxes
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    PreE7FiniteQcharAxes w i where
  width_lower := D.width_lower
  width_upper := D.width_upper
  registry := D.registry
  E := D.E
  degree := D.degree
  action := D.action
  action_injective := D.action_injective
  degree_window := D.degree_window
  axes :=
    { state := fun j h ↦
        ⟨(D.state j h).toLinearZmud.certificate hZmud, rfl, by
          simpa only [PreE7LinearZmudTupleData.certificate_slope] using
            D.state_capacity j h⟩ }

@[simp] theorem toAxes_degree
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    (D.toAxes hZmud).degree = D.degree := rfl

@[simp] theorem toAxes_mainCoefficient
    (hZmud : ZmudFaithfulCharacterTupleInput) (j : D.registry.State) :
    (D.toAxes hZmud).template.mainCoefficient
        (D.registry.normalAxis j) = D.mainCoefficient j :=
  rfl

@[simp] theorem toAxes_tailCoefficient
    (hZmud : ZmudFaithfulCharacterTupleInput) (j : D.registry.State) :
    (D.toAxes hZmud).template.tailCoefficient
        (D.registry.normalAxis j) = D.tailCoefficient j :=
  rfl

end PreE7FiniteQcharZmudAxes

/-- Numerically complete finite QCHAR row, again with the arbitrary normal
axis sums reduced to sums over the emitted registry states. -/
structure PreE7FiniteQcharMenuData
    (w : ℕ) (i : PreE7NonPairActionClass w) : Type 1 where
  axes : PreE7FiniteQcharAxes w i
  main_state_total_bound : ∀ b,
    (∑ j : axes.registry.State,
      axes.template.mainCoefficient (axes.registry.normalAxis j)) ≤
        (2 : ℝ) ^
          (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)
  tail_state_total_bound : ∀ b,
    (∑ j : axes.registry.State,
      axes.template.tailCoefficient (axes.registry.normalAxis j)) ≤
        (2 : ℝ) ^
          (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)

namespace PreE7FiniteQcharMenuData

variable {w : ℕ} {i : PreE7NonPairActionClass w}
  (D : PreE7FiniteQcharMenuData w i)

noncomputable def menuData :
    PreE7CharacterMenuSourceData .qchar (by rfl) w i where
  source := D.axes.qcharSource
  main_total_bound b := by
    rw [D.axes.registry.fusionAxisEnvelopeTotal_eq_stateSum]
    exact D.main_state_total_bound b
  tail_total_bound b := by
    rw [D.axes.registry.fusionAxisEnvelopeTotal_eq_stateSum]
    exact D.tail_state_total_bound b

/-- The comparator row enters the same final source boundary as the mixed
row, through the audited QCHAR family. -/
noncomputable def rankTailSource :
    PreE7RankTailSourceOrYonedaTopData w i :=
  .inl (.ordinary .qchar (.character (by rfl) D.menuData))

end PreE7FiniteQcharMenuData

/-- A complete selected QCHAR package whose character representations are
created from finite linear/Zmud data at final assembly time. -/
structure PreE7FiniteQcharZmudMenuData
    (w : ℕ) (i : PreE7NonPairActionClass w) : Type 1 where
  axes : PreE7FiniteQcharZmudAxes w i
  main_state_total_bound : ∀ b,
    (∑ j : axes.registry.State,
      axes.mainCoefficient j) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)
  tail_state_total_bound : ∀ b,
    (∑ j : axes.registry.State,
      axes.tailCoefficient j) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)

namespace PreE7FiniteQcharZmudMenuData

variable {w : ℕ} {i : PreE7NonPairActionClass w}
  (D : PreE7FiniteQcharZmudMenuData w i)

/-- Materialize the ordinary finite QCHAR payload from one compact selected
package and the published Zmud theorem. -/
noncomputable def toMenuData
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    PreE7FiniteQcharMenuData w i where
  axes := D.axes.toAxes hZmud
  main_state_total_bound := by
    intro b
    simpa only [PreE7FiniteQcharZmudAxes.toAxes_mainCoefficient] using
      D.main_state_total_bound b
  tail_state_total_bound := by
    intro b
    simpa only [PreE7FiniteQcharZmudAxes.toAxes_tailCoefficient] using
      D.tail_state_total_bound b

@[simp] theorem toMenuData_degree
    (hZmud : ZmudFaithfulCharacterTupleInput) :
    (D.toMenuData hZmud).axes.degree = D.axes.degree := rfl

end PreE7FiniteQcharZmudMenuData

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
