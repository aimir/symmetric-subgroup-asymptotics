import SymmetricSubgroupAsymptotics.Non2PreE7NoPairNoC3EarlierComparators
import SymmetricSubgroupAsymptotics.BinaryCharacterEnvelope
import SymmetricSubgroupAsymptotics.KovacsPraegerAbelianization
import SymmetricSubgroupAsymptotics.FusionQuotientComparator
import SymmetricSubgroupAsymptotics.TrivialQuotientComparator

/-!
# The character-certificate template for the pre-E7 earlier owners

The eight historical character families FCHAR, MCHAR, BCHAR, HCHAR, DCHAR,
JCHAR, QCHAR and B4CHAR share one estimate.  Fix, before any complementary
source `J ≤ S_b` is seen, a jointly faithful tuple of complex characters on
every literal normal quotient `U/N` outside a retained interval `[E, U]`.
Inflating the fixed tuple along the onto maps `J → U/N` labels their
kernels, so

`Epi(J, U/N) ≤ |Aut(U/N)| · |Lin₂(J)|^r · |Lin(J)|^l · k(J)^t`,

and the retained interval is charged to one comparator.  The published
class-number and abelian-quotient bounds turn this into a per-axis
additive envelope with a pure cold tail.

This file proves the template once.  Its input `PreE7CharacterTemplateData`
retains the literal action, every literal normal axis, the interval
comparator and a fixed certificate on each remaining quotient.  Its output is
the frozen `PreE7EarlierActionComparatorCertificate`, together with every
per-entry numerical condition of the additive-tail transfer at the global
`ρ = 1/8192`.

Capacity is stated in the Lean window `slope ≤ halfDegree w / 4 - ρ w / 4`,
which is exactly the tail gap of the transfer.  The historical fixed-width
capacity `slope ≤ h(w)/8 - 1/64` implies this window only for `w ≤ 512`.

The literature enters only through `PreE7CharacterLiterature`: Garonzi and
Maróti's class-number theorem, the Kovács--Praeger abelian-quotient bounds
and Maróti's nilpotent class-number theorem.  Each is a named hypothesis,
not an axiom.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-! ## Literature interfaces -/

/-- Garonzi--Maróti, *On the number of conjugacy classes of a permutation
group*, J. Combin. Theory Ser. A 133 (2015), 251--260, Theorem 1.1 (p. 1):
a permutation group of degree `b ≥ 4` has at most `5^((b-1)/3)` conjugacy
classes.  This is a named literature hypothesis, not an axiom; the uniform
form `k(J) ≤ 5^(b/3)` for every `b` is proved below. -/
def GaronziMarotiConjugacyClassBound : Prop :=
  ∀ (b : ℕ), 4 ≤ b → ∀ J : Subgroup (Equiv.Perm (Fin b)),
    (Nat.card (ConjClasses J) : ℝ) ≤ (5 : ℝ) ^ (((b : ℝ) - 1) / 3)

/-- Kovács--Praeger, *Finite permutation groups with large abelian
quotients*, Pacific J. Math. 136 (1989), unnumbered Theorem on p. 283 at the
prime `2` (register entry LIT-KP): if a Sylow `2`-subgroup of a permutation
group moves `m₂` points, the largest abelian `2`-quotient of the group has
order at most `2^(m₂/2)`.  Only the consequence `m₂ ≤ b` is recorded.  This is a named
literature hypothesis, not an axiom. -/
def KovacsPraegerBinaryAbelianQuotientBound : Prop :=
  ∀ (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) (A : Type) [CommGroup A]
    [Finite A], IsPGroup 2 A → ∀ φ : J →* A, Function.Surjective φ →
      (Nat.card A : ℝ) ≤ (2 : ℝ) ^ ((b : ℝ) / 2)

/-- The four published inputs of the character template. -/
structure PreE7CharacterLiterature : Prop where
  garonziMaroti : GaronziMarotiConjugacyClassBound
  kovacsPraeger : KovacsPraegerAbelianizationBound
  kovacsPraegerBinary : KovacsPraegerBinaryAbelianQuotientBound
  maroti : NilpotentConjugacyClassInput

/-- A finite noncommutative group has fewer conjugacy classes than
elements. -/
theorem card_conjClasses_lt_of_not_commute {G : Type*} [Group G] [Finite G]
    {x y : G} (hxy : x * y ≠ y * x) :
    Nat.card (ConjClasses G) < Nat.card G := by
  letI := Fintype.ofFinite G
  letI := Fintype.ofFinite (ConjClasses G)
  have hsurj : Function.Surjective (ConjClasses.mk : G → ConjClasses G) :=
    ConjClasses.mk_surjective
  have hninj : ¬ Function.Injective (ConjClasses.mk : G → ConjClasses G) := by
    intro hinj
    have hconj : ConjClasses.mk (y * x * y⁻¹) = ConjClasses.mk x :=
      ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨y⁻¹, by group⟩)
    have hyx := hinj hconj
    apply hxy
    calc x * y = y * x * y⁻¹ * y := by rw [hyx]
      _ = y * x := by group
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_lt_of_surjective_not_injective _ hsurj hninj

private theorem conjClasses_card_le_card {G : Type*} [Group G] [Finite G] :
    Nat.card (ConjClasses G) ≤ Nat.card G :=
  Nat.card_le_card_of_surjective _ ConjClasses.mk_surjective

private theorem two_le_five_rpow_two_thirds :
    (2 : ℝ) ≤ (5 : ℝ) ^ ((2 : ℝ) / 3) := by
  rw [Real.le_rpow_iff_log_le (by norm_num) (by norm_num)]
  have h : Real.log 8 ≤ Real.log 25 :=
    Real.log_le_log (by norm_num) (by norm_num)
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have h25 : Real.log 25 = 2 * Real.log 5 := by
    rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [h8, h25] at h
  linarith

/-- The uniform class-number interface `k(J) ≤ 5^(b/3)` for every degree,
from Garonzi--Maróti for `b ≥ 4` and direct checks for `b ≤ 3`. -/
theorem conjClasses_card_le_five_rpow
    (hGM : GaronziMarotiConjugacyClassBound)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (ConjClasses J) : ℝ) ≤ (5 : ℝ) ^ ((b : ℝ) / 3) := by
  by_cases hb : 4 ≤ b
  · refine (hGM b hb J).trans ?_
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  · have hcardJ : Nat.card J ≤ Nat.card (Equiv.Perm (Fin b)) :=
      Nat.card_le_card_of_injective _ Subtype.val_injective
    rw [Nat.card_perm, Nat.card_fin] at hcardJ
    have hk := (conjClasses_card_le_card (G := J)).trans hcardJ
    interval_cases b
    · have : Nat.card (ConjClasses J) ≤ 1 := by simpa using hk
      calc (Nat.card (ConjClasses J) : ℝ) ≤ 1 := by exact_mod_cast this
        _ = (5 : ℝ) ^ (((0 : ℕ) : ℝ) / 3) := by norm_num
    · have : Nat.card (ConjClasses J) ≤ 1 := by simpa using hk
      calc (Nat.card (ConjClasses J) : ℝ) ≤ 1 := by exact_mod_cast this
        _ ≤ (5 : ℝ) ^ (((1 : ℕ) : ℝ) / 3) :=
          Real.one_le_rpow (by norm_num) (by norm_num)
    · have : Nat.card (ConjClasses J) ≤ 2 := by simpa using hk
      calc (Nat.card (ConjClasses J) : ℝ) ≤ 2 := by exact_mod_cast this
        _ ≤ (5 : ℝ) ^ ((2 : ℝ) / 3) := two_le_five_rpow_two_thirds
        _ = (5 : ℝ) ^ (((2 : ℕ) : ℝ) / 3) := by norm_num
    · have h5 : Nat.card (ConjClasses J) ≤ 5 := by
        have h3 : Nat.factorial 3 = 6 := rfl
        have hJ : Nat.card J ≤ 6 := h3 ▸ hcardJ
        rcases Nat.lt_or_ge (Nat.card J) 6 with hlt | hge
        · exact (conjClasses_card_le_card (G := J)).trans (by omega)
        · have h6 : Nat.card J = 6 := by omega
          have htop : J = ⊤ := by
            apply Subgroup.eq_top_of_card_eq
            rw [h6, Nat.card_perm, Nat.card_fin, h3]
          subst htop
          let x : (⊤ : Subgroup (Equiv.Perm (Fin 3))) :=
            ⟨Equiv.swap 0 1, Subgroup.mem_top _⟩
          let y : (⊤ : Subgroup (Equiv.Perm (Fin 3))) :=
            ⟨Equiv.swap 1 2, Subgroup.mem_top _⟩
          have hxy : x * y ≠ y * x := by
            intro h
            have h' := congrArg Subtype.val h
            revert h'
            decide
          have := card_conjClasses_lt_of_not_commute hxy
          omega
      calc (Nat.card (ConjClasses J) : ℝ) ≤ 5 := by exact_mod_cast h5
        _ = (5 : ℝ) ^ (((3 : ℕ) : ℝ) / 3) := by norm_num

/-! ## Counting linear character labels -/

/-- A `ℂˣ`-valued character of a finite commutative group, read as an
additive character of its additive form. -/
def unitsCharacterAddChar (A : Type*) [CommGroup A] (χ : A →* ℂˣ) :
    AddChar (Additive A) ℂ where
  toFun a := ((χ (Additive.toMul a) : ℂˣ) : ℂ)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a c := by simp [toMul_add]

theorem unitsCharacterAddChar_injective (A : Type*) [CommGroup A] :
    Function.Injective (unitsCharacterAddChar A) := by
  intro χ ψ h
  ext a
  have := DFunLike.congr_fun h (Additive.ofMul a)
  simpa [unitsCharacterAddChar] using this

theorem addChar_additive_card_eq (A : Type*) [CommGroup A] [Finite A] :
    Nat.card (AddChar (Additive A) ℂ) = Nat.card A := by
  letI : Fintype (Additive A) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, AddChar.card_eq, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr Additive.toMul

/-- Every finite set of linear complex characters of a finite group injects
into the complex characters of its abelianization. -/
theorem linearCharacterSet_card_le_abelianization
    {G : Type*} [Group G] [Finite G] (S : Set (G →* ℂˣ)) :
    Nat.card S ≤ Nat.card (Abelianization G) := by
  let e : S → AddChar (Additive (Abelianization G)) ℂ :=
    fun χ => unitsCharacterAddChar (Abelianization G)
      (Abelianization.lift χ.1)
  have he : Function.Injective e := by
    intro χ ψ h
    apply Subtype.ext
    exact Abelianization.lift.injective
      (unitsCharacterAddChar_injective (Abelianization G) h)
  exact (Nat.card_le_card_of_injective e he).trans_eq
    (addChar_additive_card_eq (Abelianization G))

/-- Binary-primary linear characters are counted by one actual abelian
`2`-quotient: the joint image of the whole finite set. -/
theorem binaryLinearCharacterSet_card_le
    (hKP₂ : KovacsPraegerBinaryAbelianQuotientBound)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b)))
    (S : Set (J →* ℂˣ)) [Finite S]
    (hS : ∀ χ ∈ S, IsPGroup 2 χ.range) :
    (Nat.card S : ℝ) ≤ (2 : ℝ) ^ ((b : ℝ) / 2) := by
  letI := Fintype.ofFinite S
  let Φ : J →* (S → ℂˣ) := Pi.monoidHom (fun χ : S => χ.1)
  let A : Subgroup (S → ℂˣ) := Φ.range
  letI : Finite A := Finite.of_surjective Φ.rangeRestrict
    Φ.rangeRestrict_surjective
  have hA : IsPGroup 2 A := by
    rintro ⟨a, x, rfl⟩
    have hk : ∀ χ : S, ∃ k : ℕ, (χ.1 x) ^ 2 ^ k = 1 := by
      intro χ
      obtain ⟨k, hk⟩ := hS χ.1 χ.2 ⟨χ.1 x, x, rfl⟩
      exact ⟨k, congrArg Subtype.val hk⟩
    choose k hk using hk
    refine ⟨∑ χ, k χ, ?_⟩
    apply Subtype.ext
    funext χ
    change (χ.1 x) ^ 2 ^ (∑ χ, k χ) = 1
    obtain ⟨m, hm⟩ : 2 ^ k χ ∣ 2 ^ (∑ χ, k χ) :=
      pow_dvd_pow 2 (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ χ))
    rw [hm, pow_mul, hk χ, one_pow]
  have hcardA := hKP₂ b J A hA Φ.rangeRestrict Φ.rangeRestrict_surjective
  let e : S → AddChar (Additive A) ℂ :=
    fun χ => unitsCharacterAddChar A
      ((Pi.evalMonoidHom (fun _ : S => ℂˣ) χ).comp A.subtype)
  have he : Function.Injective e := by
    intro χ ψ h
    have h' := unitsCharacterAddChar_injective A h
    apply Subtype.ext
    ext x
    have := DFunLike.congr_fun h' ⟨Φ x, x, rfl⟩
    simpa [Φ] using congrArg Units.val this
  have hcard := (Nat.card_le_card_of_injective e he).trans_eq
    (addChar_additive_card_eq A)
  exact (by exact_mod_cast hcard : (Nat.card S : ℝ) ≤ Nat.card A).trans hcardA


/-- Maróti's nilpotent class-number bound applied to an actual Sylow
subgroup, for every prime. -/
theorem originalSylow_conjugacyClass_bound_of_prime
    (hMaroti : NilpotentConjugacyClassInput) {p : ℕ} [Fact p.Prime]
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) (P : Sylow p J) :
    (Nat.card (ConjClasses (P : Subgroup J)) : ℝ) ≤ (38 / 25 : ℝ) ^ b := by
  let T := (P : Subgroup J).map J.subtype
  let e : (P : Subgroup J) ≃* T :=
    Subgroup.equivMapOfInjective (P : Subgroup J) J.subtype
      Subtype.val_injective
  have hT : IsPGroup p T := P.isPGroup'.of_equiv e
  have hn : Group.IsNilpotent T := hT.isNilpotent
  have hc : Nat.card (ConjClasses (P : Subgroup J)) ≤
      Nat.card (ConjClasses T) :=
    Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
      (ConjClasses.map_surjective e.symm.surjective)
  exact (by exact_mod_cast hc : (Nat.card (ConjClasses (P : Subgroup J)) : ℝ) ≤
    (Nat.card (ConjClasses T) : ℝ)).trans (hMaroti b T hn)

/-! ## Designated character tuples on one literal quotient -/

/-- A jointly faithful tuple of complex characters on one fixed quotient,
with three designated categories of positions: binary-primary linear
characters (every value of `2`-power order), unrestricted linear characters,
and general irreducible representations.  Designation only selects the
count used for that position; a general position may be linear. -/
structure CharacterSlotTuple (Q : Type) [Group Q] : Type 1 where
  binaryCount : ℕ
  linearCount : ℕ
  generalCount : ℕ
  binary : Fin binaryCount → Q →* ℂˣ
  binary_twoGroup : ∀ i, IsPGroup 2 (binary i).range
  linear : Fin linearCount → Q →* ℂˣ
  general : Fin generalCount → FiniteIrreducibleRepresentation ℂ Q
  faithful : ∀ q : Q, (∀ i, binary i q = 1) → (∀ i, linear i q = 1) →
    (∀ i, (general i).action q = 1) → q = 1

section Labels

variable {J Q : Type} [Group J] [Group Q] [Finite J] [Finite Q]

theorem groupEpimorphism_finite : Finite (GroupEpimorphism J Q) :=
  Finite.of_injective (fun f : GroupEpimorphism J Q => (f.1 : J → Q))
    (fun _ _ h => Subtype.ext (DFunLike.coe_injective h))

/-- The inflations of one fixed linear character along all onto maps. -/
def linearCharacterLabels (χ : Q →* ℂˣ) : Set (J →* ℂˣ) :=
  Set.range (fun f : GroupEpimorphism J Q => χ.comp f.1)

instance linearCharacterLabels_finite (χ : Q →* ℂˣ) :
    Finite (linearCharacterLabels (J := J) χ) := by
  letI := groupEpimorphism_finite (J := J) (Q := Q)
  unfold linearCharacterLabels
  infer_instance

omit [Finite J] [Finite Q] in
theorem linearCharacterLabels_twoGroup (χ : Q →* ℂˣ)
    (hχ : IsPGroup 2 χ.range) :
    ∀ ψ ∈ linearCharacterLabels (J := J) χ, IsPGroup 2 ψ.range := by
  rintro ψ ⟨f, rfl⟩
  apply hχ.to_le
  rintro _ ⟨x, rfl⟩
  exact ⟨f.1 x, rfl⟩

omit [Finite Q] in
theorem representation_comp_ker_eq_of_character_eq
    [Invertible (Nat.card J : ℂ)] (ρ : FiniteIrreducibleRepresentation ℂ Q)
    (f g : GroupEpimorphism J Q)
    (h : Representation.character (ρ.action.comp f.1) =
      Representation.character (ρ.action.comp g.1)) :
    (ρ.action.comp f.1).ker = (ρ.action.comp g.1).ker := by
  letI := Fintype.ofFinite J
  letI : Representation.IsIrreducible (ρ.action.comp f.1) :=
    representation_irreducible_comp ρ.action f.1 f.2
  letI : Representation.IsIrreducible (ρ.action.comp g.1) :=
    representation_irreducible_comp ρ.action g.1 g.2
  obtain ⟨e⟩ := irreducible_equiv_of_character_eq
    (ρ.action.comp f.1) (ρ.action.comp g.1) h
  exact representation_kernel_eq_of_equiv e

/-- The label of an onto map on the complete source: all linear positions
by their inflated characters and all general positions by their inflated
character functions. -/
def CharacterSlotTuple.mixedLabel [Invertible (Nat.card J : ℂ)]
    (T : CharacterSlotTuple Q) (f : GroupEpimorphism J Q) :
    (∀ i, linearCharacterLabels (J := J) (T.binary i)) ×
      (∀ i, linearCharacterLabels (J := J) (T.linear i)) ×
      (∀ i, epimorphismCharacterLabels (J := J) (T.general i).action) :=
  (fun i => ⟨(T.binary i).comp f.1, f, rfl⟩,
    fun i => ⟨(T.linear i).comp f.1, f, rfl⟩,
    fun i => ⟨Representation.character ((T.general i).action.comp f.1), f, rfl⟩)

omit [Finite J] [Finite Q] in
/-- Equal source values of every designated position force equal onto
kernels, by joint faithfulness of the fixed target tuple. -/
theorem CharacterSlotTuple.ker_eq_of_values (T : CharacterSlotTuple Q)
    {H : Type} [Group H] (f g : H →* Q)
    (hb : ∀ i, (T.binary i).comp f = (T.binary i).comp g)
    (hl : ∀ i, (T.linear i).comp f = (T.linear i).comp g)
    (hg : ∀ i, ((T.general i).action.comp f).ker =
      ((T.general i).action.comp g).ker) :
    f.ker = g.ker := by
  have hone : ∀ (f g : H →* Q),
      (∀ i, (T.binary i).comp f = (T.binary i).comp g) →
      (∀ i, (T.linear i).comp f = (T.linear i).comp g) →
      (∀ i, ((T.general i).action.comp f).ker =
        ((T.general i).action.comp g).ker) →
      ∀ x, f x = 1 → g x = 1 := by
    intro f g hb hl hg x hx
    apply T.faithful
    · intro i
      have := DFunLike.congr_fun (hb i) x
      simp only [MonoidHom.comp_apply, hx, map_one] at this
      exact this.symm
    · intro i
      have := DFunLike.congr_fun (hl i) x
      simp only [MonoidHom.comp_apply, hx, map_one] at this
      exact this.symm
    · intro i
      have hm : x ∈ ((T.general i).action.comp f).ker := by
        change (T.general i).action (f x) = 1
        rw [hx, map_one]
      rw [hg i] at hm
      exact hm
  ext x
  exact ⟨hone f g hb hl hg x,
    hone g f (fun i => (hb i).symm) (fun i => (hl i).symm)
      (fun i => (hg i).symm) x⟩

theorem CharacterSlotTuple.mixedLabel_ker [Invertible (Nat.card J : ℂ)]
    (T : CharacterSlotTuple Q) (f g : GroupEpimorphism J Q)
    (h : T.mixedLabel f = T.mixedLabel g) :
    f.1.ker = g.1.ker := by
  obtain ⟨hb, hl, hg⟩ := Prod.ext_iff.mp h |>.imp id Prod.ext_iff.mp
  apply T.ker_eq_of_values f.1 g.1
  · intro i
    exact congrArg Subtype.val (congrFun hb i)
  · intro i
    exact congrArg Subtype.val (congrFun hl i)
  · intro i
    exact representation_comp_ker_eq_of_character_eq (T.general i) f g
      (congrArg Subtype.val (congrFun hg i))

/-- The finite label count on the complete source. -/
theorem CharacterSlotTuple.card_le_mixedLabels [Invertible (Nat.card J : ℂ)]
    (T : CharacterSlotTuple Q) :
    Nat.card (GroupEpimorphism J Q) ≤
      ((∏ i, Nat.card (linearCharacterLabels (J := J) (T.binary i))) *
        (∏ i, Nat.card (linearCharacterLabels (J := J) (T.linear i))) *
        (∏ i, Nat.card
          (epimorphismCharacterLabels (J := J) (T.general i).action))) *
        Nat.card (Q ≃* Q) := by
  have h := groupEpimorphism_card_le_kernel_labels (T.mixedLabel (J := J))
    (T.mixedLabel_ker)
  simpa only [Nat.card_prod, Nat.card_pi, mul_assoc] using h

/-- Restriction to one actual Sylow subgroup, for a target `p`-group. -/
def CharacterSlotTuple.knownLabel {p : ℕ} [Fact p.Prime]
    (T : CharacterSlotTuple Q) (P : Sylow p J) (hQ : IsPGroup p Q)
    [Invertible (Nat.card (P : Subgroup J) : ℂ)]
    (f : GroupEpimorphism J Q) :
    (∀ i, linearCharacterLabels (J := J) (T.binary i)) ×
      (∀ i, linearCharacterLabels (J := J) (T.linear i)) ×
      (∀ i, epimorphismCharacterLabels (J := (P : Subgroup J))
        (T.general i).action) :=
  (fun i => ⟨(T.binary i).comp f.1, f, rfl⟩,
    fun i => ⟨(T.linear i).comp f.1, f, rfl⟩,
    fun i => ⟨Representation.character ((T.general i).action.comp
      (sylowEpimorphismRestriction P hQ f).1), _, rfl⟩)

theorem CharacterSlotTuple.knownLabel_ker {p : ℕ} [Fact p.Prime]
    (T : CharacterSlotTuple Q) (P : Sylow p J) (hQ : IsPGroup p Q)
    [Invertible (Nat.card (P : Subgroup J) : ℂ)]
    (f g : GroupEpimorphism J Q)
    (h : T.knownLabel P hQ f = T.knownLabel P hQ g) :
    f.1.ker = g.1.ker := by
  obtain ⟨hb, hl, hg⟩ := Prod.ext_iff.mp h |>.imp id Prod.ext_iff.mp
  let f' := sylowEpimorphismRestriction P hQ f
  let g' := sylowEpimorphismRestriction P hQ g
  have hker : f'.1.ker = g'.1.ker := by
    apply T.ker_eq_of_values f'.1 g'.1
    · intro i
      have := congrArg Subtype.val (congrFun hb i)
      change (T.binary i).comp f.1 = (T.binary i).comp g.1 at this
      change ((T.binary i).comp f.1).comp (P : Subgroup J).subtype =
        ((T.binary i).comp g.1).comp (P : Subgroup J).subtype
      rw [this]
    · intro i
      have := congrArg Subtype.val (congrFun hl i)
      change (T.linear i).comp f.1 = (T.linear i).comp g.1 at this
      change ((T.linear i).comp f.1).comp (P : Subgroup J).subtype =
        ((T.linear i).comp g.1).comp (P : Subgroup J).subtype
      rw [this]
    · intro i
      exact representation_comp_ker_eq_of_character_eq (T.general i) f' g'
        (congrArg Subtype.val (congrFun hg i))
  let α := epimorphismChangeTarget f' g' hker
  have hcomp : α.toMonoidHom.comp f.1 = g.1 := by
    apply sylow_pGroup_hom_restriction_injective P hQ
    ext x
    exact epimorphismChangeTarget_apply f' g' hker x
  rw [← hcomp]
  ext x
  change f.1 x = 1 ↔ α (f.1 x) = 1
  exact α.map_eq_one_iff.symm

theorem CharacterSlotTuple.card_le_knownLabels {p : ℕ} [Fact p.Prime]
    (T : CharacterSlotTuple Q) (P : Sylow p J) (hQ : IsPGroup p Q)
    [Invertible (Nat.card (P : Subgroup J) : ℂ)] :
    Nat.card (GroupEpimorphism J Q) ≤
      ((∏ i, Nat.card (linearCharacterLabels (J := J) (T.binary i))) *
        (∏ i, Nat.card (linearCharacterLabels (J := J) (T.linear i))) *
        (∏ i, Nat.card
          (epimorphismCharacterLabels (J := (P : Subgroup J))
            (T.general i).action))) *
        Nat.card (Q ≃* Q) := by
  have h := groupEpimorphism_card_le_kernel_labels (T.knownLabel (J := J) P hQ)
    (T.knownLabel_ker P hQ)
  simpa only [Nat.card_prod, Nat.card_pi, mul_assoc] using h

end Labels


/-! ## Per-quotient certificates and their envelopes -/

/-- How the general positions of a quotient certificate are counted: on
the complete source (`k(J) ≤ 5^(b/3)`), or, for a target `p`-group, on one
actual Sylow `p`-subgroup of the source (`k(P) ≤ (38/25)^b`). -/
inductive CharacterQuotientMode
  | mixed
  | knownPGroup
  deriving DecidableEq

/-- Binary exponent paid by one general position. -/
def CharacterQuotientMode.generalSlope : CharacterQuotientMode → ℝ
  | .mixed => Real.logb 2 5 / 3
  | .knownPGroup => Real.logb 2 (38 / 25)

/-- A fixed certificate on one literal quotient: a designated jointly
faithful tuple, and in the known-preimage mode an actual prime for which the
quotient is a `p`-group. -/
structure CharacterQuotientCertificate (Q : Type) [Group Q] : Type 1 where
  mode : CharacterQuotientMode
  tuple : CharacterSlotTuple Q
  prime : ℕ
  known : mode = .knownPGroup → prime.Prime ∧ IsPGroup prime Q

/-- The exact binary exponent of the certificate envelope. -/
def CharacterQuotientCertificate.slope {Q : Type} [Group Q]
    (c : CharacterQuotientCertificate Q) : ℝ :=
  (c.tuple.binaryCount : ℝ) * (1 / 2) +
    (c.tuple.linearCount : ℝ) * (Real.logb 2 3 / 3) +
    (c.tuple.generalCount : ℝ) * c.mode.generalSlope

private theorem rpow_eq_two_rpow_logb {B : ℝ} (hB : 0 < B) (x : ℝ) :
    B ^ x = (2 : ℝ) ^ (Real.logb 2 B * x) := by
  rw [Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hB]

private theorem prod_card_le_two_rpow {n : ℕ} (c : Fin n → ℕ) (s : ℝ) (b : ℕ)
    (hc : ∀ i, (c i : ℝ) ≤ (2 : ℝ) ^ (s * b)) :
    ((∏ i, c i : ℕ) : ℝ) ≤ (2 : ℝ) ^ (((n : ℝ) * s) * b) := by
  push_cast
  calc ∏ i, (c i : ℝ) ≤ ∏ _i : Fin n, (2 : ℝ) ^ (s * b) :=
        Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _) (fun i _ => hc i)
    _ = ((2 : ℝ) ^ (s * b)) ^ n := by simp
    _ = (2 : ℝ) ^ (((n : ℝ) * s) * b) := by
        rw [← Real.rpow_mul_natCast (by norm_num)]
        ring_nf

private theorem envelope_combine {e a x y z : ℕ} {sx sy sz : ℝ} {b : ℕ}
    (h : e ≤ (x * y * z) * a)
    (hx : (x : ℝ) ≤ (2 : ℝ) ^ (sx * b)) (hy : (y : ℝ) ≤ (2 : ℝ) ^ (sy * b))
    (hz : (z : ℝ) ≤ (2 : ℝ) ^ (sz * b)) :
    (e : ℝ) ≤ (a : ℝ) * (2 : ℝ) ^ ((sx + sy + sz) * b) := by
  have hcast : (e : ℝ) ≤ (x : ℝ) * y * z * a := by exact_mod_cast h
  have hxyz : (x : ℝ) * y * z ≤
      (2 : ℝ) ^ (sx * b) * (2 : ℝ) ^ (sy * b) * (2 : ℝ) ^ (sz * b) := by
    apply mul_le_mul (mul_le_mul hx hy (by positivity) (by positivity)) hz
      (by positivity) (by positivity)
  have hsum : (2 : ℝ) ^ (sx * b) * (2 : ℝ) ^ (sy * b) * (2 : ℝ) ^ (sz * b) =
      (2 : ℝ) ^ ((sx + sy + sz) * b) := by
    rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
    ring_nf
  calc (e : ℝ) ≤ (x : ℝ) * y * z * a := hcast
    _ ≤ (2 : ℝ) ^ ((sx + sy + sz) * b) * a := by
        rw [← hsum]
        exact mul_le_mul_of_nonneg_right hxyz (by positivity)
    _ = _ := mul_comm _ _

/-- The complete-source envelope of one quotient certificate:
`Epi(J,Q) ≤ |Aut Q| · 2^(slope·b)` for every actual `J ≤ S_b`. -/
theorem CharacterQuotientCertificate.envelope
    (lit : PreE7CharacterLiterature) {Q : Type} [Group Q] [Finite Q]
    (c : CharacterQuotientCertificate Q) (b : ℕ)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
      (Nat.card (Q ≃* Q) : ℝ) * (2 : ℝ) ^ (c.slope * b) := by
  letI : Invertible (Nat.card J : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast (Nat.card_pos (α := J)).ne')
  have hbin : ((∏ i, Nat.card (linearCharacterLabels (J := J)
      (c.tuple.binary i)) : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (((c.tuple.binaryCount : ℝ) * (1 / 2)) * b) := by
    apply prod_card_le_two_rpow
    intro i
    have h := binaryLinearCharacterSet_card_le lit.kovacsPraegerBinary b J
      (linearCharacterLabels (J := J) (c.tuple.binary i))
      (linearCharacterLabels_twoGroup _ (c.tuple.binary_twoGroup i))
    refine h.trans_eq ?_
    congr 1
    ring
  have hlin : ((∏ i, Nat.card (linearCharacterLabels (J := J)
      (c.tuple.linear i)) : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (((c.tuple.linearCount : ℝ) * (Real.logb 2 3 / 3)) * b) := by
    apply prod_card_le_two_rpow
    intro i
    have h1 := linearCharacterSet_card_le_abelianization
      (linearCharacterLabels (J := J) (c.tuple.linear i))
    have h2 := lit.kovacsPraeger b J
    calc (Nat.card (linearCharacterLabels (J := J) (c.tuple.linear i)) : ℝ)
        ≤ Nat.card (Abelianization J) := by exact_mod_cast h1
      _ ≤ (3 : ℝ) ^ ((b : ℝ) / 3) := h2
      _ = _ := by
          rw [rpow_eq_two_rpow_logb (by norm_num)]
          congr 1
          ring
  cases hmode : c.mode with
  | mixed =>
    have hgen : ((∏ i, Nat.card (epimorphismCharacterLabels (J := J)
        (c.tuple.general i).action) : ℕ) : ℝ) ≤
        (2 : ℝ) ^ (((c.tuple.generalCount : ℝ) * (Real.logb 2 5 / 3)) * b) := by
      apply prod_card_le_two_rpow
      intro i
      have h1 := epimorphismCharacterLabels_card (J := J)
        (c.tuple.general i).action
      have h2 := conjClasses_card_le_five_rpow lit.garonziMaroti b J
      calc (Nat.card (epimorphismCharacterLabels (J := J)
            (c.tuple.general i).action) : ℝ)
          ≤ Nat.card (ConjClasses J) := by exact_mod_cast h1
        _ ≤ (5 : ℝ) ^ ((b : ℝ) / 3) := h2
        _ = _ := by
            rw [rpow_eq_two_rpow_logb (by norm_num)]
            congr 1
            ring
    have h := envelope_combine (c.tuple.card_le_mixedLabels (J := J))
      hbin hlin hgen
    refine h.trans_eq ?_
    unfold CharacterQuotientCertificate.slope
    rw [hmode]
    rfl
  | knownPGroup =>
    obtain ⟨hp, hQ⟩ := c.known hmode
    haveI : Fact c.prime.Prime := ⟨hp⟩
    let P : Sylow c.prime J := Classical.choice inferInstance
    letI : Invertible (Nat.card (P : Subgroup J) : ℂ) :=
      invertibleOfNonzero
        (by exact_mod_cast (Nat.card_pos (α := (P : Subgroup J))).ne')
    have hgen : ((∏ i, Nat.card (epimorphismCharacterLabels
        (J := (P : Subgroup J)) (c.tuple.general i).action) : ℕ) : ℝ) ≤
        (2 : ℝ) ^ (((c.tuple.generalCount : ℝ) *
          Real.logb 2 (38 / 25)) * b) := by
      apply prod_card_le_two_rpow
      intro i
      have h1 := epimorphismCharacterLabels_card (J := (P : Subgroup J))
        (c.tuple.general i).action
      have h2 := originalSylow_conjugacyClass_bound_of_prime lit.maroti b J P
      calc (Nat.card (epimorphismCharacterLabels (J := (P : Subgroup J))
            (c.tuple.general i).action) : ℝ)
          ≤ Nat.card (ConjClasses (P : Subgroup J)) := by exact_mod_cast h1
        _ ≤ (38 / 25 : ℝ) ^ b := h2
        _ = (38 / 25 : ℝ) ^ (b : ℝ) := (Real.rpow_natCast _ _).symm
        _ = _ := by
            rw [rpow_eq_two_rpow_logb (by norm_num)]
    have h := envelope_combine (c.tuple.card_le_knownLabels (J := J) P hQ)
      hbin hlin hgen
    refine h.trans_eq ?_
    unfold CharacterQuotientCertificate.slope
    rw [hmode]
    rfl

/-! ## The retained comparator interval -/

/-- How a retained interval `[E, U]` is charged to its comparator. -/
inductive CharacterIntervalOrigin
  | whole
  | quotientAction
  | externalEnvelope
  deriving DecidableEq

/-- One comparator for the whole retained normal interval above `E`.  On
every literal axis `N ⊇ E` the original onto maps are bounded by a
comparator-weighted term and a pure cold tail. -/
structure CharacterIntervalComparator {w : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w))) (E : Subgroup U) [E.Normal] :
    Type 1 where
  origin : CharacterIntervalOrigin
  R : Type
  [groupR : Group R]
  [finiteR : Finite R]
  degree : ℕ
  action : R →* Equiv.Perm (Fin degree)
  action_injective : Function.Injective action
  coefficient : ℝ
  eta : ℝ
  tail : ℝ
  tailSlope : ℝ
  coefficient_nonneg : 0 ≤ coefficient
  eta_nonneg : 0 ≤ eta
  tail_nonneg : 0 ≤ tail
  bound : ∀ (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b)))
      (N : {N : Subgroup U // N.Normal}), E ≤ N.1 →
    (Nat.card (GroupEpimorphism J (U ⧸ N.1)) : ℝ) ≤
      (coefficient * (2 : ℝ) ^ (eta * b)) *
          completeQuotientWeight (R := R) J +
        tail * (2 : ℝ) ^ (tailSlope * b)
  whole_spec : origin = .whole → E = ⊤
  quotient_spec : origin = .quotientAction →
    coefficient = 1 ∧ eta = 0 ∧ tail = 0 ∧ Nonempty (R ≃* U ⧸ E)

attribute [instance] CharacterIntervalComparator.groupR
  CharacterIntervalComparator.finiteR

/-- Onto maps to one literal quotient of `R` are one summand of its
complete quotient weight. -/
theorem card_groupEpimorphism_le_completeQuotientWeight
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) {Q R : Type*} [Group Q]
    [Group R] [Finite R] (M : {M : Subgroup R // M.Normal})
    (e : Q ≃* R ⧸ M.1) :
    (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
      completeQuotientWeight (R := R) J := by
  have htransport : Nat.card (GroupEpimorphism J Q) =
      Nat.card (GroupEpimorphism J (R ⧸ M.1)) :=
    fusionGroupEpimorphism_card_congr (MulEquiv.refl J) e
  have haxis : Nat.card (GroupEpimorphism J (R ⧸ M.1)) ≤
      completeQuotientCount (R := R) J := by
    unfold completeQuotientCount
    exact Finset.single_le_sum
      (fun M _ => Nat.zero_le (Nat.card (GroupEpimorphism J (R ⧸ M.1))))
      (Finset.mem_univ M)
  unfold completeQuotientWeight
  exact_mod_cast htransport.le.trans haxis

namespace CharacterIntervalComparator

variable {w : ℕ} {U : Subgroup (Equiv.Perm (Fin w))} {E : Subgroup U}
  [E.Normal]

/-- The whole group is the only axis above `E = U`; its quotient is trivial
and the trivial comparator counts it exactly once. -/
def whole (hE : E = ⊤) : CharacterIntervalComparator U E where
  origin := .whole
  R := PUnit
  degree := 0
  action := 1
  action_injective := fun _ _ _ => Subsingleton.elim _ _
  coefficient := 1
  eta := 0
  tail := 0
  tailSlope := 0
  coefficient_nonneg := zero_le_one
  eta_nonneg := le_rfl
  tail_nonneg := le_rfl
  bound := by
    intro b J N hN
    have hN' : N.1 = ⊤ := top_unique (hE ▸ hN)
    haveI : Subsingleton (U ⧸ N.1) := by
      constructor
      intro x y
      induction x using QuotientGroup.induction_on with | H x => ?_
      induction y using QuotientGroup.induction_on with | H y => ?_
      rw [QuotientGroup.eq, hN']
      trivial
    haveI : Subsingleton (GroupEpimorphism J (U ⧸ N.1)) :=
      ⟨fun f g => Subtype.ext (MonoidHom.ext fun _ => Subsingleton.elim _ _)⟩
    have hle : Nat.card (GroupEpimorphism J (U ⧸ N.1)) ≤ 1 :=
      Finite.card_le_one_iff_subsingleton.mpr inferInstance
    rw [completeQuotientWeight_eq_one_of_subsingleton (R := PUnit) J]
    have : (Nat.card (GroupEpimorphism J (U ⧸ N.1)) : ℝ) ≤ 1 := by
      exact_mod_cast hle
    simpa using this
  whole_spec := fun _ => hE
  quotient_spec := fun h => nomatch h

/-- The literal quotient `U/E` with a supplied faithful action.  By normal
correspondence every axis above `E` is one summand of `Z_J(U/E)`, with
coefficient one and no automorphism factor. -/
def ofQuotientAction (v₀ : ℕ) (act : U ⧸ E →* Equiv.Perm (Fin v₀))
    (hact : Function.Injective act) : CharacterIntervalComparator U E where
  origin := .quotientAction
  R := U ⧸ E
  degree := v₀
  action := act
  action_injective := hact
  coefficient := 1
  eta := 0
  tail := 0
  tailSlope := 0
  coefficient_nonneg := zero_le_one
  eta_nonneg := le_rfl
  tail_nonneg := le_rfl
  bound := by
    intro b J N hN
    let M : {M : Subgroup (U ⧸ E) // M.Normal} :=
      ⟨N.1.map (QuotientGroup.mk' E), inferInstance⟩
    have h := card_groupEpimorphism_le_completeQuotientWeight J M
      (QuotientGroup.quotientQuotientEquivQuotient E N.1 hN).symm
    simpa using h
  whole_spec := fun h => nomatch h
  quotient_spec := fun _ => ⟨rfl, rfl, rfl, ⟨MulEquiv.refl _⟩⟩

/-- A comparator certified by an independently proved additive envelope
for the interval above `E`. -/
def ofExternalEnvelope (R : Type) [Group R] [Finite R] (v₀ : ℕ)
    (act : R →* Equiv.Perm (Fin v₀)) (hact : Function.Injective act)
    (coefficient eta tail tailSlope : ℝ) (hcoefficient : 0 ≤ coefficient)
    (heta : 0 ≤ eta) (htail : 0 ≤ tail)
    (hbound : ∀ (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b)))
      (N : {N : Subgroup U // N.Normal}), E ≤ N.1 →
      (Nat.card (GroupEpimorphism J (U ⧸ N.1)) : ℝ) ≤
        (coefficient * (2 : ℝ) ^ (eta * b)) *
            completeQuotientWeight (R := R) J +
          tail * (2 : ℝ) ^ (tailSlope * b)) :
    CharacterIntervalComparator U E where
  origin := .externalEnvelope
  R := R
  degree := v₀
  action := act
  action_injective := hact
  coefficient := coefficient
  eta := eta
  tail := tail
  tailSlope := tailSlope
  coefficient_nonneg := hcoefficient
  eta_nonneg := heta
  tail_nonneg := htail
  bound := hbound
  whole_spec := fun h => nomatch h
  quotient_spec := fun h => nomatch h

end CharacterIntervalComparator


/-! ## Padding a comparator action by fixed points -/

/-- The first `m` points of `Fin n`. -/
def characterComparatorPadEquiv {m n : ℕ} (h : m ≤ n) :
    Fin m ≃ {x : Fin n // (x : ℕ) < m} where
  toFun i := ⟨Fin.castLE h i, i.isLt⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Extend permutations of the first `m` points by fixing the rest. -/
def characterComparatorPadHom {m n : ℕ} (h : m ≤ n) :
    Equiv.Perm (Fin m) →* Equiv.Perm (Fin n) :=
  Equiv.Perm.extendDomainHom (characterComparatorPadEquiv h)

theorem characterComparatorPadHom_injective {m n : ℕ} (h : m ≤ n) :
    Function.Injective (characterComparatorPadHom h) :=
  Equiv.Perm.extendDomainHom_injective _

namespace Non2UnipotentPrefixFiniteMenu

/-! ## The global window -/

/-- The single global comparator fraction of the pre-E7 transfer. -/
def preE7CharacterRho : ℝ := 1 / 8192

/-- The Lean capacity window: exactly the cold tail gap of the additive
transfer at `ρ = 1/8192`. -/
def preE7CharacterWindow (w : ℕ) : ℝ :=
  (halfDegree w : ℝ) / 4 - preE7CharacterRho * w / 4

/-- The historical fixed-width capacity `slope ≤ h(w)/8 - 1/64` implies the
Lean window when `w ≤ 512`.  For larger widths the historical `1/64` margin
is smaller than `ρ w / 4` and gives no window by itself. -/
theorem preE7CharacterWindow_of_historicalCapacity {w : ℕ} (hw : w ≤ 512)
    {s : ℝ} (hs : s ≤ (halfDegree w : ℝ) / 4 - 1 / 64) :
    s ≤ preE7CharacterWindow w := by
  unfold preE7CharacterWindow preE7CharacterRho
  have : (w : ℝ) ≤ 512 := by exact_mod_cast hw
  linarith

/-! ## Template data -/

/-- One literal retained action with a fixed character certificate.  The
normal interval above `E` is charged to one comparator; every other literal
normal axis carries its own fixed quotient certificate, whose slope lies in
the Lean window.  Isomorphic quotients at distinct axes remain distinct
entries. -/
structure PreE7CharacterTemplateData (w : ℕ) (i : PreE7NonPairActionClass w) :
    Type 1 where
  width_lower : 8 ≤ w
  width_upper : w ≤ 12288
  E : Subgroup (preE7NonPairAction w i)
  [E_normal : E.Normal]
  interval : CharacterIntervalComparator (preE7NonPairAction w i) E
  interval_window : preE7CharacterRho * w ≤
    ((evenWidth w : ℝ) - ((max 2 interval.degree : ℕ) : ℝ)) / 8 -
      interval.eta
  interval_tail_window : interval.tailSlope ≤ preE7CharacterWindow w
  quotient : ∀ N : {N : Subgroup (preE7NonPairAction w i) // N.Normal},
    ¬ E ≤ N.1 → CharacterQuotientCertificate (preE7NonPairAction w i ⧸ N.1)
  capacity : ∀ N h, (quotient N h).slope ≤ preE7CharacterWindow w

attribute [instance] PreE7CharacterTemplateData.E_normal

namespace PreE7CharacterTemplateData

variable {w : ℕ} {i : PreE7NonPairActionClass w}
  (D : PreE7CharacterTemplateData w i)

/-- Comparator degree before padding, with the two-point floor. -/
def sourceDegree : ℕ := max 2 D.interval.degree

/-- The padded comparator degree. -/
def degree : ℕ := paddedComparatorDegree preE7CharacterRho D.sourceDegree w

/-- The padded residual margin. -/
def delta : ℝ :=
  paddedComparatorDelta preE7CharacterRho D.interval.eta D.sourceDegree w

/-- The hot/cold threshold exponent. -/
def cutoff : ℝ := (D.degree : ℝ) / 8 + D.delta / 2

theorem interval_degree_le : D.interval.degree ≤ D.degree :=
  (le_max_right 2 D.interval.degree).trans (le_max_left _ _)

/-- Comparator coefficient: the interval coefficient above `E`, zero on the
character axes. -/
def mainCoefficient
    (N : {N : Subgroup (preE7NonPairAction w i) // N.Normal}) : ℝ :=
  if D.E ≤ N.1 then D.interval.coefficient else 0

/-- Cold tail coefficient: the interval tail above `E`, and the literal
target automorphism count on each character axis. -/
def tailCoefficient
    (N : {N : Subgroup (preE7NonPairAction w i) // N.Normal}) : ℝ :=
  if D.E ≤ N.1 then D.interval.tail
  else (Nat.card ((preE7NonPairAction w i ⧸ N.1) ≃*
    (preE7NonPairAction w i ⧸ N.1)) : ℝ)

theorem mainCoefficient_nonneg (N) : 0 ≤ D.mainCoefficient N := by
  unfold mainCoefficient
  split_ifs
  · exact D.interval.coefficient_nonneg
  · exact le_rfl

theorem tailCoefficient_nonneg (N) : 0 ≤ D.tailCoefficient N := by
  unfold tailCoefficient
  split_ifs
  · exact D.interval.tail_nonneg
  · exact Nat.cast_nonneg _

theorem fusionSurvivingEpiCount_le_card {b : ℕ}
    (P : Subgroup (preE7NonPairAction w i × Equiv.Perm (Fin b)) → Prop)
    (N : {N : Subgroup (preE7NonPairAction w i) // N.Normal})
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount (preE7NonPairAction w i) P N J ≤
      Nat.card (GroupEpimorphism J (preE7NonPairAction w i ⧸ N.1)) := by
  letI := groupEpimorphism_finite (J := J)
    (Q := preE7NonPairAction w i ⧸ N.1)
  unfold fusionSurvivingEpiCount
  exact_mod_cast Nat.card_le_card_of_injective Subtype.val
    Subtype.val_injective

/-- The per-axis additive envelope on the broad source. -/
theorem axis_envelope (lit : PreE7CharacterLiterature) (b : ℕ)
    (N : {N : Subgroup (preE7NonPairAction w i) // N.Normal})
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount (preE7NonPairAction w i)
        (preE7NoPairNoC3BroadActionPredicate w i b) N J ≤
      (D.mainCoefficient N * (2 : ℝ) ^ (D.interval.eta * b)) *
          completeQuotientWeight (R := D.interval.R) J +
        D.tailCoefficient N * (2 : ℝ) ^ (preE7CharacterWindow w * b) := by
  refine (fusionSurvivingEpiCount_le_card _ N J).trans ?_
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  by_cases hE : D.E ≤ N.1
  · simp only [mainCoefficient, tailCoefficient, if_pos hE]
    refine (D.interval.bound b J N hE).trans ?_
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_left _ D.interval.tail_nonneg
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_right D.interval_tail_window hb)
  · simp only [mainCoefficient, tailCoefficient, if_neg hE, zero_mul,
      zero_add]
    refine ((D.quotient N hE).envelope lit b J).trans ?_
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_right (D.capacity N hE) hb)

/-- The frozen family certificate produced by the character template.  The
family index is the caller's; the template content is the same for all
eight character families. -/
def certificate (lit : PreE7CharacterLiterature)
    (family : PreE7NoPairNoC3EarlierOwnerFamily) :
    PreE7EarlierActionComparatorCertificate family w i where
  R := D.interval.R
  v := D.degree
  action := (characterComparatorPadHom D.interval_degree_le).comp
    D.interval.action
  action_injective := (characterComparatorPadHom_injective _).comp
    D.interval.action_injective
  C := fun _ N => D.mainCoefficient N
  tailCoefficient := fun _ N => D.tailCoefficient N
  eta := D.interval.eta
  delta := D.delta
  cutoff := D.cutoff
  alpha := D.interval.eta + D.cutoff
  theta := preE7CharacterWindow w
  alpha_eq := rfl
  coefficient_nonneg := fun _ N => D.mainCoefficient_nonneg N
  tail_nonneg := fun _ N => D.tailCoefficient_nonneg N
  broad_axis_envelope := fun b N J => D.axis_envelope lit b N J

end PreE7CharacterTemplateData

/-! ## Per-entry numerics at the global `ρ` -/

/-- Every numerical condition which the additive-tail transfer imposes on
one retained index entry: the twelve fields of
`GrowingQuotientParameterBound` and the cold tail gap. -/
structure PreE7CharacterEntryParameters (ρ : ℝ) (w v : ℕ)
    (η δ c α θ : ℝ) : Prop where
  delta_nonneg : 0 ≤ δ
  degree_pos : 0 < v
  ratio : ρ / 2 ≤ δ / (v : ℝ)
  degree_upper : (v : ℝ) ≤ (1 - 4 * ρ) * w
  delta_lower : ρ * w / 2 ≤ δ
  hot_margin : η + c - w / 8 ≤ -δ / 2
  threshold_eq : c = (v : ℝ) / 8 + δ / 2
  delta_upper : δ ≤ (w : ℝ) / 8
  degree_lower : ρ * w ≤ (v : ℝ)
  degree_width : (v : ℝ) ≤ w
  cold_slope : α = η + c
  cold_gap : α ≤ (halfDegree w : ℝ) / 4 - ρ * w / 4
  tail_gap : θ ≤ (halfDegree w : ℝ) / 4 - ρ * w / 4

/-- Entrywise parameters assemble into the global parameter bound and the
global tail gap of the additive transfer. -/
theorem growingQuotientParameterBound_of_entryParameters
    {ι : ℕ → Type*} [∀ w, Fintype (ι w)] {ρ : ℝ}
    {v : ∀ w, ι w → ℕ} {η δ c α θ : ∀ w, ι w → ℝ}
    (h : ∀ w i, PreE7CharacterEntryParameters ρ w (v w i) (η w i) (δ w i)
      (c w i) (α w i) (θ w i)) :
    GrowingQuotientParameterBound ρ v η δ c α ∧
      ∀ w i, θ w i ≤ (halfDegree w : ℝ) / 4 - ρ * w / 4 :=
  ⟨{ delta_nonneg := fun w i => (h w i).delta_nonneg
     degree_pos := fun w i => (h w i).degree_pos
     ratio := fun w i => (h w i).ratio
     degree_upper := fun w i => (h w i).degree_upper
     delta_lower := fun w i => (h w i).delta_lower
     hot_margin := fun w i => (h w i).hot_margin
     threshold_eq := fun w i => (h w i).threshold_eq
     delta_upper := fun w i => (h w i).delta_upper
     degree_lower := fun w i => (h w i).degree_lower
     degree_width := fun w i => (h w i).degree_width
     cold_slope := fun w i => (h w i).cold_slope
     cold_gap := fun w i => (h w i).cold_gap },
    fun w i => (h w i).tail_gap⟩

/-- Every numerical fact about one certificate that the transfer and the
menu-mass aggregation consume: the entry parameters at `ρ = 1/8192`, the
fixed width cap, and coefficients bounded independently of the complement
degree. -/
structure PreE7CharacterCertificateNumerics
    {family : PreE7NoPairNoC3EarlierOwnerFamily} {w : ℕ}
    {i : PreE7NonPairActionClass w}
    (C : PreE7EarlierActionComparatorCertificate family w i) : Prop where
  parameters : PreE7CharacterEntryParameters preE7CharacterRho w C.v C.eta
    C.delta C.cutoff C.alpha C.theta
  width_upper : w ≤ 12288
  coefficient_bounded : ∃ K : ℝ, ∀ b N, C.C b N ≤ K ∧ C.tailCoefficient b N ≤ K

namespace PreE7CharacterTemplateData

variable {w : ℕ} {i : PreE7NonPairActionClass w}
  (D : PreE7CharacterTemplateData w i)

/-- The padded comparator satisfies every parameter condition at
`ρ = 1/8192`, and the tail slope is the window itself. -/
theorem entryParameters :
    PreE7CharacterEntryParameters preE7CharacterRho w D.degree
      D.interval.eta D.delta D.cutoff (D.interval.eta + D.cutoff)
      (preE7CharacterWindow w) := by
  let ι : ℕ → Type := fun w' => {_u : Unit // w' = w}
  have hP := growingPadded_parameterBound (ι := ι) (ρ := preE7CharacterRho)
    (fun _ _ => D.sourceDegree) (fun _ _ => D.interval.eta)
    (by norm_num [preE7CharacterRho]) (by norm_num [preE7CharacterRho])
    (fun _ _ => D.interval.eta_nonneg) (fun _ _ => le_max_left _ _)
    (by
      rintro w' ⟨_, rfl⟩
      exact D.interval_window)
  let j : ι w := ⟨(), rfl⟩
  exact
    { delta_nonneg := hP.delta_nonneg w j
      degree_pos := hP.degree_pos w j
      ratio := hP.ratio w j
      degree_upper := hP.degree_upper w j
      delta_lower := hP.delta_lower w j
      hot_margin := hP.hot_margin w j
      threshold_eq := hP.threshold_eq w j
      delta_upper := hP.delta_upper w j
      degree_lower := hP.degree_lower w j
      degree_width := hP.degree_width w j
      cold_slope := hP.cold_slope w j
      cold_gap := hP.cold_gap w j
      tail_gap := le_rfl }

/-- One bound for every coefficient, independent of the complement
degree. -/
theorem coefficient_bounded :
    ∃ K : ℝ, ∀ N, D.mainCoefficient N ≤ K ∧ D.tailCoefficient N ≤ K := by
  refine ⟨D.interval.coefficient + D.interval.tail +
    ∑ N : {N : Subgroup (preE7NonPairAction w i) // N.Normal},
      (Nat.card ((preE7NonPairAction w i ⧸ N.1) ≃*
        (preE7NonPairAction w i ⧸ N.1)) : ℝ), fun N => ?_⟩
  have hsum : (0 : ℝ) ≤
      ∑ N : {N : Subgroup (preE7NonPairAction w i) // N.Normal},
        (Nat.card ((preE7NonPairAction w i ⧸ N.1) ≃*
          (preE7NonPairAction w i ⧸ N.1)) : ℝ) :=
    Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hN : (Nat.card ((preE7NonPairAction w i ⧸ N.1) ≃*
      (preE7NonPairAction w i ⧸ N.1)) : ℝ) ≤
      ∑ N : {N : Subgroup (preE7NonPairAction w i) // N.Normal},
        (Nat.card ((preE7NonPairAction w i ⧸ N.1) ≃*
          (preE7NonPairAction w i ⧸ N.1)) : ℝ) :=
    Finset.single_le_sum (f := fun N :
      {N : Subgroup (preE7NonPairAction w i) // N.Normal} =>
        (Nat.card ((preE7NonPairAction w i ⧸ N.1) ≃*
          (preE7NonPairAction w i ⧸ N.1)) : ℝ))
      (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ N)
  have hc := D.interval.coefficient_nonneg
  have ht := D.interval.tail_nonneg
  unfold mainCoefficient tailCoefficient
  constructor <;> split_ifs <;> linarith

theorem certificate_numerics (lit : PreE7CharacterLiterature)
    (family : PreE7NoPairNoC3EarlierOwnerFamily) :
    PreE7CharacterCertificateNumerics (D.certificate lit family) where
  parameters := D.entryParameters
  width_upper := D.width_upper
  coefficient_bounded := by
    obtain ⟨K, hK⟩ := D.coefficient_bounded
    exact ⟨K, fun _ N => hK N⟩

end PreE7CharacterTemplateData

end Non2UnipotentPrefixFiniteMenu

end SymmetricSubgroupAsymptotics
