import SymmetricSubgroupAsymptotics.Non2PreE7CharacterCertificateTemplate

/-!
# The eight character families as certificate instances

Each historical character family is an existential certificate on one
literal original action: its predicate is inhabited exactly when the
family's source data below exist.  No census, precedence or earlier-family
exclusion enters.  The source data retain every literal normal quotient and
the family's permitted tuple shape:

* FCHAR: general positions only, on every quotient except `U/U`.
* MCHAR: designated linear and general positions.
* BCHAR: binary-primary linear, linear and general positions.
* HCHAR: its MIXED mode, which has the MCHAR shape.
* DCHAR and JCHAR: the BCHAR mode and the known-preimage mode, in which a
  target `p`-group counts its general positions on an actual Sylow
  subgroup of the source.
* QCHAR: the literal quotient `U/E` with a supplied faithful action carries
  the interval above `E`; linear and general positions elsewhere.
* B4CHAR: an independently proved additive envelope carries the interval
  above `E`; general positions elsewhere.

Scope.  Three historical modes are not part of these source shapes, because
their counting theorems are not yet formal: the HEAD mode of HCHAR (derived
binary head ranks), the designated-anchor mode of DCHAR and the joint-anchor
mode of JCHAR (Frobenius reciprocity over the anchor preimage).  Their
exclusion only makes the certificate predicates smaller.

Capacity is the Lean window at `ρ = 1/8192`.  The historical fixed-width
margin `1/64` implies it only for `w ≤ 512`
(`preE7CharacterWindow_of_historicalCapacity`).
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-! ## Permitted tuple shapes -/

/-- General positions only, counted on the complete source. -/
def CharacterQuotientCertificate.IsGeneralOnly {Q : Type} [Group Q]
    (c : CharacterQuotientCertificate Q) : Prop :=
  c.mode = .mixed ∧ c.tuple.binaryCount = 0 ∧ c.tuple.linearCount = 0

/-- Designated linear and general positions on the complete source. -/
def CharacterQuotientCertificate.IsLinearMixed {Q : Type} [Group Q]
    (c : CharacterQuotientCertificate Q) : Prop :=
  c.mode = .mixed ∧ c.tuple.binaryCount = 0

/-- Binary-primary, linear and general positions on the complete source. -/
def CharacterQuotientCertificate.IsBinaryMixed {Q : Type} [Group Q]
    (c : CharacterQuotientCertificate Q) : Prop :=
  c.mode = .mixed

/-- The BCHAR mode or the known-preimage mode. -/
def CharacterQuotientCertificate.IsBinaryOrKnown {Q : Type} [Group Q]
    (_c : CharacterQuotientCertificate Q) : Prop :=
  True

namespace Non2UnipotentPrefixFiniteMenu

/-- The eight families assigned to the character template. -/
def IsPreE7CharacterFamily (family : PreE7NoPairNoC3EarlierOwnerFamily) :
    Prop :=
  family.template = .character

instance : DecidablePred IsPreE7CharacterFamily := fun family =>
  inferInstanceAs (Decidable (family.template = .character))

theorem isPreE7CharacterFamily_iff
    (family : PreE7NoPairNoC3EarlierOwnerFamily) :
    IsPreE7CharacterFamily family ↔
      family = .fchar ∨ family = .mchar ∨ family = .bchar ∨
        family = .dchar ∨ family = .jchar ∨ family = .hchar ∨
        family = .qchar ∨ family = .b4char := by
  cases family <;> decide

/-! ## Family source shapes -/

/-- A fixed certificate on every literal normal quotient other than `U/U`.
This is the source shape of FCHAR, MCHAR, BCHAR, HCHAR, DCHAR and JCHAR. -/
structure CharacterWholeMenuSource (w : ℕ) (i : PreE7NonPairActionClass w)
    (Permitted : ∀ {Q : Type} [Group Q], CharacterQuotientCertificate Q → Prop) :
    Type 1 where
  width_lower : 8 ≤ w
  width_upper : w ≤ 12288
  quotient : ∀ N : {N : Subgroup (preE7NonPairAction w i) // N.Normal},
    N.1 ≠ ⊤ → CharacterQuotientCertificate (preE7NonPairAction w i ⧸ N.1)
  permitted : ∀ N h, Permitted (quotient N h)
  capacity : ∀ N h, (quotient N h).slope ≤ preE7CharacterWindow w

/-- QCHAR: a normal `E`, a supplied faithful action of the literal quotient
`U/E`, and a fixed linear/general tuple on every quotient not above `E`. -/
structure QcharSource (w : ℕ) (i : PreE7NonPairActionClass w) : Type 1 where
  width_lower : 8 ≤ w
  width_upper : w ≤ 12288
  E : Subgroup (preE7NonPairAction w i)
  [E_normal : E.Normal]
  degree : ℕ
  action : preE7NonPairAction w i ⧸ E →* Equiv.Perm (Fin degree)
  action_injective : Function.Injective action
  degree_window : preE7CharacterRho * w ≤
    ((evenWidth w : ℝ) - ((max 2 degree : ℕ) : ℝ)) / 8
  quotient : ∀ N : {N : Subgroup (preE7NonPairAction w i) // N.Normal},
    ¬ E ≤ N.1 → CharacterQuotientCertificate (preE7NonPairAction w i ⧸ N.1)
  permitted : ∀ N h, (quotient N h).IsLinearMixed
  capacity : ∀ N h, (quotient N h).slope ≤ preE7CharacterWindow w

attribute [instance] QcharSource.E_normal

/-- B4CHAR: a normal `E` whose interval is bounded by a proved additive
comparator envelope, and a fixed general tuple on every quotient not above
`E`.  In the historical family `E` is the unique minimal normal subgroup and
the envelope is the TF bound for `U/E`. -/
structure B4charSource (w : ℕ) (i : PreE7NonPairActionClass w) : Type 1 where
  width_lower : 8 ≤ w
  width_upper : w ≤ 12288
  E : Subgroup (preE7NonPairAction w i)
  [E_normal : E.Normal]
  R : Type
  [groupR : Group R]
  [finiteR : Finite R]
  degree : ℕ
  action : R →* Equiv.Perm (Fin degree)
  action_injective : Function.Injective action
  coefficient : ℝ
  tail : ℝ
  tailSlope : ℝ
  coefficient_nonneg : 0 ≤ coefficient
  tail_nonneg : 0 ≤ tail
  bound : ∀ (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b)))
      (N : {N : Subgroup (preE7NonPairAction w i) // N.Normal}), E ≤ N.1 →
    (Nat.card (GroupEpimorphism J (preE7NonPairAction w i ⧸ N.1)) : ℝ) ≤
      coefficient * completeQuotientWeight (R := R) J +
        tail * (2 : ℝ) ^ (tailSlope * b)
  degree_window : preE7CharacterRho * w ≤
    ((evenWidth w : ℝ) - ((max 2 degree : ℕ) : ℝ)) / 8
  tail_window : tailSlope ≤ preE7CharacterWindow w
  quotient : ∀ N : {N : Subgroup (preE7NonPairAction w i) // N.Normal},
    ¬ E ≤ N.1 → CharacterQuotientCertificate (preE7NonPairAction w i ⧸ N.1)
  permitted : ∀ N h, (quotient N h).IsGeneralOnly
  capacity : ∀ N h, (quotient N h).slope ≤ preE7CharacterWindow w

attribute [instance] B4charSource.E_normal B4charSource.groupR
  B4charSource.finiteR

/-- The source data accepted by each character family.  Every other family
has no character source. -/
def CharacterCertificateSourceData :
    PreE7NoPairNoC3EarlierOwnerFamily →
      ∀ w, PreE7NonPairActionClass w → Type 1
  | .fchar => fun w i => CharacterWholeMenuSource w i
      CharacterQuotientCertificate.IsGeneralOnly
  | .mchar => fun w i => CharacterWholeMenuSource w i
      CharacterQuotientCertificate.IsLinearMixed
  | .bchar => fun w i => CharacterWholeMenuSource w i
      CharacterQuotientCertificate.IsBinaryMixed
  | .hchar => fun w i => CharacterWholeMenuSource w i
      CharacterQuotientCertificate.IsLinearMixed
  | .dchar => fun w i => CharacterWholeMenuSource w i
      CharacterQuotientCertificate.IsBinaryOrKnown
  | .jchar => fun w i => CharacterWholeMenuSource w i
      CharacterQuotientCertificate.IsBinaryOrKnown
  | .qchar => fun w i => QcharSource w i
  | .b4char => fun w i => B4charSource w i
  | _ => fun _ _ => PEmpty

/-! ## Conversion to the template -/

/-- The trivial interval `[U, U]` meets both windows at every width at
least eight. -/
theorem characterWhole_windows {w : ℕ} (hw : 8 ≤ w) :
    preE7CharacterRho * w ≤
        ((evenWidth w : ℝ) - ((max 2 0 : ℕ) : ℝ)) / 8 - 0 ∧
      (0 : ℝ) ≤ preE7CharacterWindow w := by
  have heven : (w : ℝ) ≤ evenWidth w + 1 := by
    exact_mod_cast width_le_evenWidth_add_one w
  have hhalf : (w : ℝ) ≤ 2 * halfDegree w + 1 := by
    have : w ≤ 2 * halfDegree w + 1 := by
      unfold halfDegree
      omega
    exact_mod_cast this
  have hw' : (8 : ℝ) ≤ w := by exact_mod_cast hw
  unfold preE7CharacterWindow preE7CharacterRho
  norm_num
  constructor <;> linarith

/-- QCHAR's historical comparator condition `v < h(w)` meets the
comparator window at `ρ = 1/8192` whenever `w ≤ 1024`.  For larger widths
the window asks for `max 2 v ≤ h(w) - w/1024`. -/
theorem qcharDegreeWindow_of_historical {w v : ℕ} (hw8 : 8 ≤ w)
    (hw : w ≤ 1024) (hv : v < evenWidth w) :
    preE7CharacterRho * w ≤ ((evenWidth w : ℝ) - ((max 2 v : ℕ) : ℝ)) / 8 := by
  have heven : 8 ≤ evenWidth w := by
    unfold evenWidth halfDegree
    omega
  have hmax : max 2 v + 1 ≤ evenWidth w := by omega
  have hmax' : ((max 2 v : ℕ) : ℝ) + 1 ≤ evenWidth w := by exact_mod_cast hmax
  have hw' : (w : ℝ) ≤ 1024 := by exact_mod_cast hw
  unfold preE7CharacterRho
  linarith

namespace CharacterWholeMenuSource

variable {w : ℕ} {i : PreE7NonPairActionClass w}
  {Permitted : ∀ {Q : Type} [Group Q], CharacterQuotientCertificate Q → Prop}

/-- The whole-menu shape is the template with `E = U`. -/
def toTemplateData (S : CharacterWholeMenuSource w i Permitted) :
    PreE7CharacterTemplateData w i where
  width_lower := S.width_lower
  width_upper := S.width_upper
  E := ⊤
  interval := CharacterIntervalComparator.whole rfl
  interval_window := (characterWhole_windows S.width_lower).1
  interval_tail_window := (characterWhole_windows S.width_lower).2
  quotient N h := S.quotient N (fun hN => h (hN ▸ le_rfl))
  capacity N _ := S.capacity N _

end CharacterWholeMenuSource

namespace QcharSource

variable {w : ℕ} {i : PreE7NonPairActionClass w}

/-- QCHAR is the template with the literal-quotient comparator. -/
def toTemplateData (S : QcharSource w i) : PreE7CharacterTemplateData w i where
  width_lower := S.width_lower
  width_upper := S.width_upper
  E := S.E
  interval := CharacterIntervalComparator.ofQuotientAction S.degree S.action
    S.action_injective
  interval_window := by
    simpa [CharacterIntervalComparator.ofQuotientAction] using S.degree_window
  interval_tail_window := (characterWhole_windows S.width_lower).2
  quotient := S.quotient
  capacity := S.capacity

end QcharSource

namespace B4charSource

variable {w : ℕ} {i : PreE7NonPairActionClass w}

/-- B4CHAR is the template with an external comparator envelope. -/
def toTemplateData (S : B4charSource w i) : PreE7CharacterTemplateData w i where
  width_lower := S.width_lower
  width_upper := S.width_upper
  E := S.E
  interval := CharacterIntervalComparator.ofExternalEnvelope S.R S.degree
    S.action S.action_injective S.coefficient 0 S.tail S.tailSlope
    S.coefficient_nonneg le_rfl S.tail_nonneg (by
      intro b J N hN
      simpa using S.bound b J N hN)
  interval_window := by
    simpa [CharacterIntervalComparator.ofExternalEnvelope] using
      S.degree_window
  interval_tail_window := S.tail_window
  quotient := S.quotient
  capacity := S.capacity

end B4charSource

/-! ## The eight family certificates -/

variable {w : ℕ} {i : PreE7NonPairActionClass w}

/-- The template data of a FCHAR source. -/
def fcharTemplateData (S : CharacterCertificateSourceData .fchar w i) :
    PreE7CharacterTemplateData w i :=
  CharacterWholeMenuSource.toTemplateData
    (Permitted := CharacterQuotientCertificate.IsGeneralOnly) S

/-- The template data of a MCHAR source. -/
def mcharTemplateData (S : CharacterCertificateSourceData .mchar w i) :
    PreE7CharacterTemplateData w i :=
  CharacterWholeMenuSource.toTemplateData
    (Permitted := CharacterQuotientCertificate.IsLinearMixed) S

/-- The template data of a BCHAR source. -/
def bcharTemplateData (S : CharacterCertificateSourceData .bchar w i) :
    PreE7CharacterTemplateData w i :=
  CharacterWholeMenuSource.toTemplateData
    (Permitted := CharacterQuotientCertificate.IsBinaryMixed) S

/-- The template data of a HCHAR source. -/
def hcharTemplateData (S : CharacterCertificateSourceData .hchar w i) :
    PreE7CharacterTemplateData w i :=
  CharacterWholeMenuSource.toTemplateData
    (Permitted := CharacterQuotientCertificate.IsLinearMixed) S

/-- The template data of a DCHAR source. -/
def dcharTemplateData (S : CharacterCertificateSourceData .dchar w i) :
    PreE7CharacterTemplateData w i :=
  CharacterWholeMenuSource.toTemplateData
    (Permitted := CharacterQuotientCertificate.IsBinaryOrKnown) S

/-- The template data of a JCHAR source. -/
def jcharTemplateData (S : CharacterCertificateSourceData .jchar w i) :
    PreE7CharacterTemplateData w i :=
  CharacterWholeMenuSource.toTemplateData
    (Permitted := CharacterQuotientCertificate.IsBinaryOrKnown) S

/-- The template data of a QCHAR source. -/
def qcharTemplateData (S : CharacterCertificateSourceData .qchar w i) :
    PreE7CharacterTemplateData w i :=
  QcharSource.toTemplateData S

/-- The template data of a B4CHAR source. -/
def b4charTemplateData (S : CharacterCertificateSourceData .b4char w i) :
    PreE7CharacterTemplateData w i :=
  B4charSource.toTemplateData S

section FamilyCertificates

variable (lit : PreE7CharacterLiterature)

/-- FCHAR (D0393). -/
def preE7_fcharCertificate (S : CharacterCertificateSourceData .fchar w i) :
    PreE7EarlierActionComparatorCertificate .fchar w i :=
  (fcharTemplateData S).certificate lit .fchar

/-- MCHAR (D0394). -/
def preE7_mcharCertificate (S : CharacterCertificateSourceData .mchar w i) :
    PreE7EarlierActionComparatorCertificate .mchar w i :=
  (mcharTemplateData S).certificate lit .mchar

/-- BCHAR (D0399). -/
def preE7_bcharCertificate (S : CharacterCertificateSourceData .bchar w i) :
    PreE7EarlierActionComparatorCertificate .bchar w i :=
  (bcharTemplateData S).certificate lit .bchar

/-- HCHAR (D0400), MIXED mode. -/
def preE7_hcharCertificate (S : CharacterCertificateSourceData .hchar w i) :
    PreE7EarlierActionComparatorCertificate .hchar w i :=
  (hcharTemplateData S).certificate lit .hchar

/-- DCHAR (D0401), BCHAR and known-preimage modes. -/
def preE7_dcharCertificate (S : CharacterCertificateSourceData .dchar w i) :
    PreE7EarlierActionComparatorCertificate .dchar w i :=
  (dcharTemplateData S).certificate lit .dchar

/-- JCHAR (D0407), BCHAR and known-preimage modes. -/
def preE7_jcharCertificate (S : CharacterCertificateSourceData .jchar w i) :
    PreE7EarlierActionComparatorCertificate .jchar w i :=
  (jcharTemplateData S).certificate lit .jchar

/-- QCHAR (D0396). -/
def preE7_qcharCertificate (S : CharacterCertificateSourceData .qchar w i) :
    PreE7EarlierActionComparatorCertificate .qchar w i :=
  (qcharTemplateData S).certificate lit .qchar

/-- B4CHAR (D0392). -/
def preE7_b4charCertificate (S : CharacterCertificateSourceData .b4char w i) :
    PreE7EarlierActionComparatorCertificate .b4char w i :=
  (b4charTemplateData S).certificate lit .b4char

end FamilyCertificates

/-- The template data underlying a character-family source. -/
def CharacterCertificateSourceData.toTemplateData
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (hfamily : IsPreE7CharacterFamily family)
    (S : CharacterCertificateSourceData family w i) :
    PreE7CharacterTemplateData w i := by
  cases family
  all_goals first
    | exact absurd hfamily (by decide)
    | skip
  case fchar => exact fcharTemplateData S
  case mchar => exact mcharTemplateData S
  case bchar => exact bcharTemplateData S
  case hchar => exact hcharTemplateData S
  case dchar => exact dcharTemplateData S
  case jchar => exact jcharTemplateData S
  case qchar => exact qcharTemplateData S
  case b4char => exact b4charTemplateData S

/-- The dispatcher over the eight character families. -/
def preE7_characterCertificate
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (hfamily : IsPreE7CharacterFamily family) (w : ℕ)
    (i : PreE7NonPairActionClass w)
    (hsource : CharacterCertificateSourceData family w i)
    (lit : PreE7CharacterLiterature) :
    PreE7EarlierActionComparatorCertificate family w i := by
  cases family
  all_goals first
    | exact absurd hfamily (by decide)
    | skip
  case fchar => exact preE7_fcharCertificate lit hsource
  case mchar => exact preE7_mcharCertificate lit hsource
  case bchar => exact preE7_bcharCertificate lit hsource
  case hchar => exact preE7_hcharCertificate lit hsource
  case dchar => exact preE7_dcharCertificate lit hsource
  case jchar => exact preE7_jcharCertificate lit hsource
  case qchar => exact preE7_qcharCertificate lit hsource
  case b4char => exact preE7_b4charCertificate lit hsource

/-- The dispatcher is the template certificate of the underlying data. -/
theorem preE7_characterCertificate_eq
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (hfamily : IsPreE7CharacterFamily family) (w : ℕ)
    (i : PreE7NonPairActionClass w)
    (hsource : CharacterCertificateSourceData family w i)
    (lit : PreE7CharacterLiterature) :
    preE7_characterCertificate family hfamily w i hsource lit =
      (CharacterCertificateSourceData.toTemplateData family hfamily
        hsource).certificate lit family := by
  cases family <;> first
    | exact absurd hfamily (by decide)
    | rfl

/-- Every dispatched certificate meets the transfer parameters at
`ρ = 1/8192`, the tail gap, the fixed width cap and a complement-independent
coefficient bound. -/
theorem preE7_characterCertificate_numerics
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (hfamily : IsPreE7CharacterFamily family) (w : ℕ)
    (i : PreE7NonPairActionClass w)
    (hsource : CharacterCertificateSourceData family w i)
    (lit : PreE7CharacterLiterature) :
    PreE7CharacterCertificateNumerics
      (preE7_characterCertificate family hfamily w i hsource lit) := by
  rw [preE7_characterCertificate_eq]
  exact PreE7CharacterTemplateData.certificate_numerics _ lit family

/-- The concrete earlier-family action predicate holds for every character
family carrying its source data. -/
theorem preE7_characterFamilyAction
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (hfamily : IsPreE7CharacterFamily family) (w : ℕ)
    (i : PreE7NonPairActionClass w)
    (hsource : CharacterCertificateSourceData family w i)
    (lit : PreE7CharacterLiterature) :
    preE7NoPairNoC3EarlierFamilyAction family w i :=
  ⟨preE7_characterCertificate family hfamily w i hsource lit⟩

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

