import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveBlockTransfer
import SymmetricSubgroupAsymptotics.ElementaryGroupSocle
import SymmetricSubgroupAsymptotics.FiniteSocleNormalGenerators
import SymmetricSubgroupAsymptotics.NormalGeneratorTypeSharing
import SymmetricSubgroupAsymptotics.PrimePrimarySocleTypeSharing
import SymmetricSubgroupAsymptotics.PrimeRelativeHeadZeroAbsorption
import SymmetricSubgroupAsymptotics.PrimeFrattiniGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineMediumOddSource
import SymmetricSubgroupAsymptotics.SocleNormalGeneratorNumber
import SymmetricSubgroupAsymptotics.SocleGeneratorCharacterInterval

/-!
# Socle generators for the degree-nine affine component

This file isolates the group-theoretic interface used by the exceptional
degree-nine affine frame.  The retained subgroup is the literal translation
intersection supplied by `PrimitiveAffineImprimitiveBlockTransfer`; its
quotient has the faithful action on the eight nonzero vectors in each block.

The zero-core argument filters the socle of every literal quotient through a
normal subgroup.  The first result below proves the needed kernel--image
subadditivity for the project's least normal-generator number.  It is useful
beyond degree nine: generators of the socle intersection and generators of
its image in the quotient can be chosen independently and then joined in the
original group.

The remaining definitions package the exact degree-nine budgets:

* `s` slots in the nonzero-core branch;
* `s + s / 3` slots in the zero-core branch (equal to `8` and `16` at the
  only surviving counts `s = 6, 12`).

No counting theorem or affine classification statement is assumed here.
The constructors consume proved normal-generator inequalities on the literal
quotients and turn them into the complete character interval used by the
pre-`E7` source.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative commutatorElement

namespace SymmetricSubgroupAsymptotics

private abbrev LiteralNormalAxis (G : Type) [Group G] :=
  {N : Subgroup G // N.Normal}

/-! ## Normal generation through a normal cut -/

namespace MarkedC4

/-! The following two cardinal lemmas keep later affine arguments on the
literal subgroup and literal quotient map.  In particular, neither replaces
an actual translation intersection by the full coordinate product. -/

/-- A subgroup cannot have larger cardinality than an overgroup. -/
theorem natCard_le_of_subgroup_le
    {G : Type} [Group G] [Finite G]
    (H K : Subgroup G) (hHK : H ≤ K) :
    Nat.card H ≤ Nat.card K := by
  exact Nat.card_le_card_of_injective (Subgroup.inclusion hHK)
    (Subgroup.inclusion_injective hHK)

/-- The literal image of a finite subgroup has cardinality at most that of
the subgroup.  This is deliberately stated for an arbitrary homomorphism so
that it applies both to the normal quotient and to the top projection. -/
theorem natCard_map_le
    {G H : Type} [Group G] [Group H] [Finite G]
    (S : Subgroup G) (f : G →* H) :
    Nat.card (S.map f) ≤ Nat.card S := by
  let toImage : S → S.map f := fun x => ⟨f x.1, ⟨x.1, x.2, rfl⟩⟩
  have hsurj : Function.Surjective toImage := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hxS, rfl⟩ := hy
    exact ⟨⟨x, hxS⟩, rfl⟩
  exact Nat.card_le_card_of_surjective toImage hsurj

/-- Cardinal factor counting for an ambient-normal semisimple subgroup.
The action-specific input is reduced to the intrinsic statement that this
subgroup is its own socle. -/
theorem normalGen_normalSubgroup_le_of_selfSocle_card
    {G : Type} [Group G] [Finite G]
    (H : Subgroup G) [H.Normal]
    (m t : ℕ) (hm : 2 ≤ m)
    (hself : finiteGroupSocle H = ⊤)
    (hmin : ∀ M : Subgroup H, IsMinimalNormalSubgroup M →
      m ≤ Nat.card M)
    (hcard : Nat.card H ≤ m ^ t) :
    normalGen H ≤ t := by
  refine (normalGen_normalSubgroup_le_internal H).trans ?_
  rw [← hself]
  apply normalGen_finiteGroupSocle_le_of_card H m t hm hmin
  rw [hself]
  simpa using hcard

/-- Normal-generator number is subadditive under joins of ambient-normal
subgroups. -/
theorem normalGen_sup_le_add
    {G : Type} [Group G] [Finite G]
    (A B : Subgroup G) [A.Normal] [B.Normal] :
    normalGen (A ⊔ B) ≤ normalGen A + normalGen B := by
  obtain ⟨a, haCard, haA, haClosure⟩ := normalGen_spec A
  obtain ⟨b, hbCard, hbB, hbClosure⟩ := normalGen_spec B
  let T : Finset G := a ∪ b
  have hTsub : (T : Set G) ⊆ (A ⊔ B : Subgroup G) := by
    intro x hx
    simp only [T, Finset.coe_union, Set.mem_union] at hx
    exact hx.elim
      (fun h => (show A ≤ A ⊔ B from le_sup_left) (haA h))
      (fun h => (show B ≤ A ⊔ B from le_sup_right) (hbB h))
  have hclosure : Subgroup.normalClosure (T : Set G) = A ⊔ B := by
    apply le_antisymm
    · exact Subgroup.normalClosure_le_normal hTsub
    · apply sup_le
      · rw [← haClosure]
        apply Subgroup.normalClosure_mono
        intro x hx
        simp only [T, Finset.coe_union, Set.mem_union]
        exact Or.inl hx
      · rw [← hbClosure]
        apply Subgroup.normalClosure_mono
        intro x hx
        simp only [T, Finset.coe_union, Set.mem_union]
        exact Or.inr hx
  calc
    normalGen (A ⊔ B) ≤ T.card := normalGen_le hTsub hclosure
    _ ≤ a.card + b.card := Finset.card_union_le a b
    _ = normalGen A + normalGen B := by rw [haCard, hbCard]

/-- Normal generation of a socle is subadditive across an arbitrary normal
cut.  The quotient term is the literal image of the socle, so the statement
does not require the cut to lie in the socle. -/
theorem normalGen_normal_le_inter_add_image
    {G : Type} [Group G] [Finite G]
    (S : Subgroup G) [S.Normal]
    (E : Subgroup G) [E.Normal] :
    normalGen S ≤
      normalGen (S ⊓ E) +
        normalGen (S.map (QuotientGroup.mk' E)) := by
  let K : Subgroup G := S ⊓ E
  let q : G →* G ⧸ E := QuotientGroup.mk' E
  haveI : K.Normal := by dsimp [K]; infer_instance
  haveI : (S.map q).Normal :=
    Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective E)
  obtain ⟨a, haCard, haK, haClosure⟩ := normalGen_spec K
  obtain ⟨b, hbCard, hbImage, hbClosure⟩ := normalGen_spec (S.map q)
  have hker : ∀ x ∈ S, q x = 1 → x ∈ K := by
    intro x hxS hxq
    refine ⟨hxS, ?_⟩
    exact (QuotientGroup.eq_one_iff x).mp hxq
  obtain ⟨c, hcCard, hcS, hcStep⟩ :=
    exists_layer_lift q (QuotientGroup.mk'_surjective E)
      K S hker b hbImage hbClosure
  let T : Finset G := a ∪ c
  have hTS : (T : Set G) ⊆ S := by
    intro x hx
    simp only [T, Finset.coe_union, Set.mem_union] at hx
    exact hx.elim (fun ha => (show K ≤ S from inf_le_left) (haK ha))
      (fun hc => hcS hc)
  have hclosure : Subgroup.normalClosure (T : Set G) = S := by
    apply le_antisymm
    · exact Subgroup.normalClosure_le_normal hTS
    · refine hcStep.trans (sup_le ?_ ?_)
      · apply Subgroup.normalClosure_mono
        intro x hx
        simp only [T, Finset.coe_union, Set.mem_union]
        exact Or.inr hx
      · rw [← haClosure]
        apply Subgroup.normalClosure_mono
        intro x hx
        simp only [T, Finset.coe_union, Set.mem_union]
        exact Or.inl hx
  calc
    normalGen S ≤ T.card := normalGen_le hTS hclosure
    _ ≤ a.card + c.card := Finset.card_union_le a c
    _ ≤ a.card + b.card := Nat.add_le_add_left hcCard a.card
    _ = normalGen K + normalGen (S.map q) := by rw [haCard, hbCard]
    _ = normalGen (S ⊓ E) +
        normalGen (S.map (QuotientGroup.mk' E)) := rfl

/-- Socle specialization of `normalGen_normal_le_inter_add_image`. -/
theorem normalGen_socle_le_inter_add_image
    {G : Type} [Group G] [Finite G]
    (E : Subgroup G) [E.Normal] :
    normalGen (finiteGroupSocle G) ≤
      normalGen (finiteGroupSocle G ⊓ E) +
        normalGen ((finiteGroupSocle G).map (QuotientGroup.mk' E)) :=
  normalGen_normal_le_inter_add_image (finiteGroupSocle G) E

/-- Numerical form of `normalGen_socle_le_inter_add_image`, immediately
converted to the exact padded tuple expected by Zmud's theorem. -/
theorem socleNormalGeneratorBound_of_inter_image
    {G : Type} [Group G] [Finite G]
    (E : Subgroup G) [E.Normal] {a b : ℕ}
    (hinter : normalGen (finiteGroupSocle G ⊓ E) ≤ a)
    (himage : normalGen
      ((finiteGroupSocle G).map (QuotientGroup.mk' E)) ≤ b) :
    SocleNormalGeneratorBound G (a + b) := by
  apply (socleNormalGeneratorBound_iff_normalGen_le G (a + b)).2
  exact (normalGen_socle_le_inter_add_image E).trans
    (Nat.add_le_add hinter himage)

end MarkedC4

/-! A selected sum of ambient minimal normal `p`-subgroups is again a
`p`-group.  Normality of every factor is essential here; it is what permits
the finite joins to stay inside the prime-primary category. -/
private theorem finset_sup_isPGroup
    (p : ℕ) [Fact p.Prime]
    {G : Type} [Group G]
    (S : Finset (Subgroup G))
    (hS : ∀ M ∈ S, M.Normal ∧ IsPGroup p M) :
    IsPGroup p
      (S.sup (fun M : Subgroup G => M) : Subgroup G) := by
  induction S using Finset.induction_on with
  | empty => simpa using (IsPGroup.of_bot (p := p) (G := G))
  | @insert M S hMS ih =>
      have hM := hS M (Finset.mem_insert_self M S)
      letI : M.Normal := hM.1
      have hrest : ∀ K ∈ S, K.Normal ∧ IsPGroup p K := by
        intro K hK
        exact hS K (Finset.mem_insert_of_mem hK)
      have hSp : IsPGroup p
          (S.sup (fun K : Subgroup G => K) : Subgroup G) := ih hrest
      rw [Finset.sup_insert]
      exact hM.2.to_sup_of_normal_left hSp

theorem minimalNormalSoclePart_isPGroup
    (p : ℕ) [Fact p.Prime]
    (G : Type) [Group G] [Finite G]
    (P : Subgroup G → Prop)
    (hP : ∀ M : Subgroup G, IsMinimalNormalSubgroup M → P M →
      IsPGroup p M) :
    IsPGroup p (minimalNormalSoclePart G P) := by
  unfold minimalNormalSoclePart
  apply finset_sup_isPGroup p
  intro M hM
  have hdata := (Finset.mem_filter.mp hM).2
  exact ⟨hdata.1.1, hP M hdata.1 hdata.2⟩

/-! ## The literal degree-nine interval -/

namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- The common slot count in the nonzero-core degree-nine branch. -/
def degreeNineNonzeroCoreSlots : ℕ := Nat.card block.Points

/-- The common slot count in the zero-core degree-nine branch. -/
def degreeNineZeroCoreSlots : ℕ :=
  Nat.card block.Points + Nat.card block.Points / 3

/-- At local degree nine the elementary translation chart really has nine
elements.  This uses the literal affine profile, rather than a chosen model
of `F₃²`. -/
theorem degreeNine_chart_card
    (hr : Nat.card block.Fibre = 9) :
    Nat.card (chart block P).V = 9 := by
  calc
    Nat.card (chart block P).V =
        Nat.card (Multiplicative (chart block P).V) :=
      (Nat.card_congr Multiplicative.toAdd).symm
    _ = Nat.card P.V :=
      (Nat.card_congr (chart block P).equiv.toEquiv).symm
    _ = Nat.card block.Fibre := P.card_eq (origin block)
    _ = 9 := hr

/-- The affine profile prime at local degree nine is three. -/
theorem degreeNine_translationPrime
    (hr : Nat.card block.Fibre = 9) :
    P.p = 3 := by
  let C := chart block P
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v))
    C.equiv.symm.injective
  have hdegree : 9 = P.p ^ C.d := by
    rw [← hr]
    simpa [PrimitiveAffineProfile.ElementaryChart.d] using
      P.degree_eq_prime_pow_finrank C.equiv (origin block)
  exact (prime_pow_positive_injective (d := C.d) (e := 2)
    P.p_prime (by norm_num : Nat.Prime 3) C.d_pos (by norm_num)
      (hdegree.symm.trans (by norm_num))).1

/-- The actual translation intersection has exponent three. -/
theorem degreeNine_translation_pow_three
    (hr : Nat.card block.Fibre = 9)
    (x : E block P) : x ^ 3 = 1 := by
  have hp := degreeNine_translationPrime block P hr
  apply (translationMulEquiv block P).injective
  rw [map_pow, map_one]
  apply Multiplicative.toAdd.injective
  change 3 • ((translationMulEquiv block P x).toAdd) = 0
  rw [← hp]
  exact ZModModule.char_nsmul_eq_zero P.p _

/-- The actual translation intersection is commutative, as witnessed by its
literal additive coordinate submodule. -/
theorem degreeNine_translation_commute
    (x y : E block P) : Commute x y := by
  rw [Commute]
  apply (translationMulEquiv block P).injective
  simp only [map_mul]
  exact mul_comm _ _

/-- The actual correlated translation intersection has at most the size of
the full product of its literal local translation coordinates. -/
theorem degreeNine_translation_card_le
    (hr : Nat.card block.Fibre = 9) :
    Nat.card (E block P) ≤ 9 ^ Nat.card block.Points := by
  let C := chart block P
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v))
    C.equiv.symm.injective
  calc
    Nat.card (E block P) ≤
        Nat.card (Multiplicative
          (block.Points → (chart block P).V)) :=
      Nat.card_le_card_of_injective (coordinates block P)
        (coordinates_injective block P)
    _ = Nat.card (block.Points → (chart block P).V) :=
      Nat.card_congr Multiplicative.toAdd
    _ = Nat.card (chart block P).V ^ Nat.card block.Points := by
      rw [Nat.card_fun]
    _ = 9 ^ Nat.card block.Points := by
      rw [degreeNine_chart_card block P hr]

/-- The retained translation subgroup in an arbitrary literal normal
quotient. -/
abbrev degreeNineTranslationImage
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    Subgroup (preE7NonPairAction w U ⧸ N.1) :=
  (E block P).map (QuotientGroup.mk' N.1)

instance degreeNineTranslationImage_normal
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    (degreeNineTranslationImage block P N).Normal :=
  Subgroup.Normal.map inferInstance (QuotientGroup.mk' N.1)
    (QuotientGroup.mk'_surjective N.1)

/-- A retained normal axis (`E ≤ N` excluded) leaves a genuinely nonzero
translation image in the quotient. -/
theorem degreeNineTranslationImage_ne_bot
    (N : LiteralNormalAxis (preE7NonPairAction w U))
    (hN : ¬ E block P ≤ N.1) :
    degreeNineTranslationImage block P N ≠ ⊥ := by
  intro hbot
  apply hN
  have hle := (Subgroup.map_eq_bot_iff
    (H := E block P) (f := QuotientGroup.mk' N.1)).mp hbot
  simpa only [QuotientGroup.ker_mk'] using hle

/-- The literal quotient translation image remains commutative. -/
theorem degreeNineTranslationImage_commute
    (N : LiteralNormalAxis (preE7NonPairAction w U))
    (x y : degreeNineTranslationImage block P N) : Commute x y := by
  let q := QuotientGroup.mk' N.1
  let f : E block P →* degreeNineTranslationImage block P N :=
    q.subgroupMap (E block P)
  obtain ⟨x₀, rfl⟩ := MonoidHom.subgroupMap_surjective q (E block P) x
  obtain ⟨y₀, rfl⟩ := MonoidHom.subgroupMap_surjective q (E block P) y
  exact (degreeNine_translation_commute block P x₀ y₀).map f

/-- The literal quotient translation image still has exponent three. -/
theorem degreeNineTranslationImage_pow_three
    (hr : Nat.card block.Fibre = 9)
    (N : LiteralNormalAxis (preE7NonPairAction w U))
    (x : degreeNineTranslationImage block P N) : x ^ 3 = 1 := by
  let q := QuotientGroup.mk' N.1
  let f : E block P →* degreeNineTranslationImage block P N :=
    q.subgroupMap (E block P)
  obtain ⟨x₀, rfl⟩ := MonoidHom.subgroupMap_surjective q (E block P) x
  rw [← map_pow, degreeNine_translation_pow_three block P hr, map_one]

/-- A translation-contained ambient normal section with zero complete
relative ternary head belongs to the active action type.  This is the exact
action-theoretic replacement for an abstract ``translation type'' label. -/
theorem degreeNine_translationSection_commutator_full_of_relativeHead_zero
    (hr : Nat.card block.Fibre = 9)
    (N : LiteralNormalAxis (preE7NonPairAction w U))
    (M : Subgroup (preE7NonPairAction w U ⧸ N.1)) [M.Normal]
    (hM : M ≤ degreeNineTranslationImage block P N)
    (hzero : Module.finrank (ZMod 3)
      (primeRelativeCharacters 3 M) = 0) :
    ⁅M, (⊤ : Subgroup (preE7NonPairAction w U ⧸ N.1))⁆ = M := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  apply mixedCommutator_eq_of_exponent_prime_relativeHead_zero 3 M
  · intro m
    let x : degreeNineTranslationImage block P N := ⟨m.1, hM m.2⟩
    apply Subtype.ext
    change m.1 ^ 3 = 1
    simpa only [x] using congrArg Subtype.val
      (degreeNineTranslationImage_pow_three block P hr N x)
  · exact hzero

/-- Every quotient translation image is its own socle. -/
theorem degreeNineTranslationImage_socle_eq_top
    (hr : Nat.card block.Fibre = 9)
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    finiteGroupSocle (degreeNineTranslationImage block P N) = ⊤ := by
  letI : IsMulCommutative (degreeNineTranslationImage block P N) :=
    IsMulCommutative.of_comm fun x y =>
      (degreeNineTranslationImage_commute block P N x y).eq
  exact finiteGroupSocle_eq_top_of_prime_exponent
    (degreeNineTranslationImage block P N) 3 (by norm_num)
      (degreeNineTranslationImage_pow_three block P hr N)

/-- Any subgroup of the quotient translation image is commutative and has
exponent three.  This is the reusable form needed for the socle cut. -/
theorem degreeNineTranslationSubgroup_socle_eq_top
    (hr : Nat.card block.Fibre = 9)
    (N : LiteralNormalAxis (preE7NonPairAction w U))
    (H : Subgroup (preE7NonPairAction w U ⧸ N.1))
    (hH : H ≤ degreeNineTranslationImage block P N) :
    finiteGroupSocle H = ⊤ := by
  have hcomm : ∀ x y : H, x * y = y * x := by
    intro x y
    apply Subtype.ext
    let x' : degreeNineTranslationImage block P N := ⟨x.1, hH x.2⟩
    let y' : degreeNineTranslationImage block P N := ⟨y.1, hH y.2⟩
    change x.1 * y.1 = y.1 * x.1
    simpa only [x', y'] using congrArg Subtype.val
      (degreeNineTranslationImage_commute block P N x' y').eq
  letI : IsMulCommutative H := IsMulCommutative.of_comm hcomm
  apply finiteGroupSocle_eq_top_of_prime_exponent H 3 (by norm_num)
  intro x
  apply Subtype.ext
  let x' : degreeNineTranslationImage block P N := ⟨x.1, hH x.2⟩
  change x.1 ^ 3 = 1
  simpa only [x'] using congrArg Subtype.val
    (degreeNineTranslationImage_pow_three block P hr N x')

/-- Passing the actual translation intersection to a normal quotient cannot
increase its order. -/
theorem degreeNine_translationImage_card_le
    (hr : Nat.card block.Fibre = 9)
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    Nat.card (degreeNineTranslationImage block P N) ≤
      9 ^ Nat.card block.Points :=
  (MarkedC4.natCard_map_le (E block P)
    (QuotientGroup.mk' N.1)).trans
      (degreeNine_translation_card_le block P hr)

/-- Consequently the part of a quotient socle lying in the retained
translation image has the same literal `9^s` cardinal ceiling. -/
theorem degreeNine_socle_inter_translationImage_card_le
    (hr : Nat.card block.Fibre = 9)
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    Nat.card ↥(finiteGroupSocle (preE7NonPairAction w U ⧸ N.1) ⊓
          degreeNineTranslationImage block P N) ≤
      9 ^ Nat.card block.Points :=
  (MarkedC4.natCard_le_of_subgroup_le _ _ inf_le_right).trans
    (degreeNine_translationImage_card_le block P hr N)

/-- The translation-intersection term in the socle filtration is elementary
abelian of exponent three, hence is its own finite-group socle. -/
theorem degreeNine_socle_inter_translationImage_socle_eq_top
    (hr : Nat.card block.Fibre = 9)
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    finiteGroupSocle
      ↥(finiteGroupSocle (preE7NonPairAction w U ⧸ N.1) ⊓
        degreeNineTranslationImage block P N) = ⊤ :=
  degreeNineTranslationSubgroup_socle_eq_top block P hr N _ inf_le_right

/-- The image term in the socle filtration over the retained translation
subgroup. -/
abbrev degreeNineSocleTopImage
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    Subgroup
      ((preE7NonPairAction w U ⧸ N.1) ⧸
        degreeNineTranslationImage block P N) :=
  (finiteGroupSocle (preE7NonPairAction w U ⧸ N.1)).map
    (QuotientGroup.mk' (degreeNineTranslationImage block P N))

instance degreeNineSocleTopImage_normal
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    (degreeNineSocleTopImage block P N).Normal :=
  Subgroup.Normal.map inferInstance
    (QuotientGroup.mk' (degreeNineTranslationImage block P N))
    (QuotientGroup.mk'_surjective
      (degreeNineTranslationImage block P N))

/-! ## Canonical ambient socle type sums -/

/-- The sum of minimal normal factors lying in the literal translation
image. -/
abbrev degreeNineTranslationSoclePart
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    Subgroup (preE7NonPairAction w U ⧸ N.1) :=
  finiteGroupSoclePart (preE7NonPairAction w U ⧸ N.1)
    (degreeNineTranslationImage block P N)

/-- The complementary sum of minimal normal factors not lying in the
literal translation image. -/
abbrev degreeNineOuterSoclePart
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    Subgroup (preE7NonPairAction w U ⧸ N.1) :=
  minimalNormalSoclePart (preE7NonPairAction w U ⧸ N.1)
    (fun M => ¬ M ≤ degreeNineTranslationImage block P N)

/-- The translation and outer ambient type sums exhaust the whole quotient
socle. -/
theorem degreeNineTranslation_outer_socle_sup
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    degreeNineTranslationSoclePart block P N ⊔
        degreeNineOuterSoclePart block P N =
      finiteGroupSocle (preE7NonPairAction w U ⧸ N.1) :=
  by
    simpa only [degreeNineTranslationSoclePart, finiteGroupSoclePart,
      degreeNineOuterSoclePart] using
      (minimalNormalSoclePart_sup_compl_eq_finiteGroupSocle
        (preE7NonPairAction w U ⧸ N.1)
        (fun M => M ≤ degreeNineTranslationImage block P N))

/-- The translation type sum really stays inside the literal translation
image. -/
theorem degreeNineTranslationSoclePart_le_image
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    degreeNineTranslationSoclePart block P N ≤
      degreeNineTranslationImage block P N := by
  exact finiteGroupSoclePart_le _ _

/-- Ambient irreducible translation factors of order at least nine cost at
most one normal generator per block.  Notice that minimality is in the
literal quotient, not inside the elementary translation image. -/
theorem degreeNineTranslationSoclePart_normalGen_le
    (hr : Nat.card block.Fibre = 9)
    (N : LiteralNormalAxis (preE7NonPairAction w U))
    (hmin : ∀ M : Subgroup (preE7NonPairAction w U ⧸ N.1),
      IsMinimalNormalSubgroup M →
      M ≤ degreeNineTranslationImage block P N →
      9 ≤ Nat.card M) :
    MarkedC4.normalGen (degreeNineTranslationSoclePart block P N) ≤
      Nat.card block.Points := by
  exact normalGen_finiteGroupSoclePart_le_of_card
    (preE7NonPairAction w U ⧸ N.1)
    (degreeNineTranslationImage block P N) 9
    (Nat.card block.Points) (by norm_num) hmin
    (degreeNine_translationImage_card_le block P hr N)

/-- The ternary minimal-normal type sum in a literal quotient. -/
abbrev degreeNineTernarySoclePart
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    Subgroup (preE7NonPairAction w U ⧸ N.1) :=
  minimalNormalSoclePart (preE7NonPairAction w U ⧸ N.1)
    (fun M => IsPGroup 3 M)

/-- The complementary nonternary minimal-normal type sum. -/
abbrev degreeNineNonTernarySoclePart
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    Subgroup (preE7NonPairAction w U ⧸ N.1) :=
  minimalNormalSoclePart (preE7NonPairAction w U ⧸ N.1)
    (fun M => ¬ IsPGroup 3 M)

/-- Ternary and nonternary ambient type sums exhaust the whole quotient
socle. -/
theorem degreeNineTernary_nonTernary_socle_sup
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    degreeNineTernarySoclePart N ⊔
        degreeNineNonTernarySoclePart N =
      finiteGroupSocle (preE7NonPairAction w U ⧸ N.1) :=
  minimalNormalSoclePart_sup_compl_eq_finiteGroupSocle _
    (fun M => IsPGroup 3 M)

/-- Ternary ambient factors contained in the translation image. -/
abbrev degreeNineTernaryTranslationSoclePart
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    Subgroup (preE7NonPairAction w U ⧸ N.1) :=
  minimalNormalSoclePart (preE7NonPairAction w U ⧸ N.1)
    (fun M => IsPGroup 3 M ∧
      M ≤ degreeNineTranslationImage block P N)

/-- Ternary ambient factors outside the translation image. -/
abbrev degreeNineTernaryOuterSoclePart
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    Subgroup (preE7NonPairAction w U ⧸ N.1) :=
  minimalNormalSoclePart (preE7NonPairAction w U ⧸ N.1)
    (fun M => IsPGroup 3 M ∧
      ¬ M ≤ degreeNineTranslationImage block P N)

/-- The ternary part itself splits according to whether the ambient simple
type lies in the translation image. -/
theorem degreeNineTernary_translation_outer_sup
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    degreeNineTernaryTranslationSoclePart block P N ⊔
        degreeNineTernaryOuterSoclePart block P N =
      degreeNineTernarySoclePart N := by
  apply le_antisymm
  · apply sup_le
    · apply minimalNormalSoclePart_le_of
      intro M hM hm
      exact minimalNormal_le_minimalNormalSoclePart
        (fun K : Subgroup (preE7NonPairAction w U ⧸ N.1) => IsPGroup 3 K)
        M hM hm.1
    · apply minimalNormalSoclePart_le_of
      intro M hM hm
      exact minimalNormal_le_minimalNormalSoclePart
        (fun K : Subgroup (preE7NonPairAction w U ⧸ N.1) => IsPGroup 3 K)
        M hM hm.1
  · unfold degreeNineTernarySoclePart minimalNormalSoclePart
    apply Finset.sup_le
    intro M hM
    have hm := (Finset.mem_filter.mp hM).2
    by_cases hMF : M ≤ degreeNineTranslationImage block P N
    · exact (minimalNormal_le_minimalNormalSoclePart
          (fun K : Subgroup (preE7NonPairAction w U ⧸ N.1) =>
            IsPGroup 3 K ∧ K ≤ degreeNineTranslationImage block P N)
          M hm.1 ⟨hm.2, hMF⟩).trans le_sup_left
    · exact (minimalNormal_le_minimalNormalSoclePart
          (fun K : Subgroup (preE7NonPairAction w U ⧸ N.1) =>
            IsPGroup 3 K ∧ ¬ K ≤ degreeNineTranslationImage block P N)
          M hm.1 ⟨hm.2, hMF⟩).trans le_sup_right

/-- The only additive step in the zero-core proof is the split of the
ternary type sum at the literal translation image. -/
theorem degreeNineTernary_normalGen_le_add
    (N : LiteralNormalAxis (preE7NonPairAction w U)) :
    MarkedC4.normalGen (degreeNineTernarySoclePart N) ≤
      MarkedC4.normalGen
          (degreeNineTernaryTranslationSoclePart block P N) +
        MarkedC4.normalGen (degreeNineTernaryOuterSoclePart block P N) := by
  rw [← degreeNineTernary_translation_outer_sup block P N]
  exact MarkedC4.normalGen_sup_le_add _ _

/-- An `s`-slot translation-ternary row and an `s/3`-slot outer-ternary row
give exactly the manuscript's additive ternary budget. -/
theorem degreeNineTernary_normalGen_le_slots
    (N : LiteralNormalAxis (preE7NonPairAction w U))
    (htranslation : MarkedC4.normalGen
      (degreeNineTernaryTranslationSoclePart block P N) ≤
        Nat.card block.Points)
    (houter : MarkedC4.normalGen
      (degreeNineTernaryOuterSoclePart block P N) ≤
        Nat.card block.Points / 3) :
    MarkedC4.normalGen (degreeNineTernarySoclePart N) ≤
      Nat.card block.Points + Nat.card block.Points / 3 :=
  (degreeNineTernary_normalGen_le_add block P N).trans
    (Nat.add_le_add htranslation houter)

/-! ## The actual linear kernel and a local normal core -/

/-- The literal linear block kernel after quotienting the translations. -/
abbrev degreeNineLinearBlockKernel :
    Subgroup (preE7NonPairAction w U ⧸ E block P) :=
  ((PermutationalWreathProduct.rightHom).comp
    (quotientEmbedding block P)).ker

/-- One exact local-complement coordinate of the linear block kernel. -/
def degreeNineLinearBlockKernelCoordinate (i : block.Points) :
    degreeNineLinearBlockKernel block P →* LocalQuotient block P where
  toFun x := (quotientEmbedding block P x.1).left i
  map_one' := by simp
  map_mul' x y := by
    change (quotientEmbedding block P (x.1 * y.1)).left i =
      (quotientEmbedding block P x.1).left i *
        (quotientEmbedding block P y.1).left i
    rw [map_mul, PermutationalWreathProduct.mul_left]
    have hx : (quotientEmbedding block P x.1).right = 1 :=
      MonoidHom.mem_ker.mp x.2
    rw [hx]
    simp

/-- The quotient embedding still realizes every element of the exact local
complement over every block. -/
theorem degreeNine_quotientEmbedding_fullComponent :
    PermutationalWreathProduct.Compression.FullComponent
      (quotientEmbedding block P) := by
  intro i d
  obtain ⟨c, hc⟩ := localMap_surjective block P d
  obtain ⟨a, hai, hac⟩ :=
    ActualBlockWreathEmbedding.fullComponent
      block.map block.map_equivariant block.base i c
  refine ⟨QuotientGroup.mk' (E block P) a, ?_, ?_⟩
  · change (ambientEmbedding block a).right • i = i
    exact hai
  · change localMap block P ((ambientEmbedding block a).left i) = d
    change localMap block P
      ((ActualBlockWreathEmbedding.embedding block.map
        block.map_equivariant block.base a).left i) = d
    rw [hac, hc]

/-- Every coordinate image of the literal linear kernel is normal in the
exact local complement. -/
theorem degreeNineLinearBlockKernelCoordinate_range_normal
    (i : block.Points) :
    (degreeNineLinearBlockKernelCoordinate block P i).range.Normal := by
  constructor
  rintro x ⟨e, rfl⟩ c
  obtain ⟨a, hai, hac⟩ := degreeNine_quotientEmbedding_fullComponent block P i c
  let K := degreeNineLinearBlockKernel block P
  let z : K := ⟨a * e.1 * a⁻¹,
    (inferInstance : K.Normal).conj_mem e.1 e.2 a⟩
  refine ⟨z, ?_⟩
  change (quotientEmbedding block P (a * e.1 * a⁻¹)).left i =
    c * (quotientEmbedding block P e.1).left i * c⁻¹
  rw [map_mul, map_mul, map_inv]
  have he : (quotientEmbedding block P e.1).right = 1 :=
    MonoidHom.mem_ker.mp e.2
  rw [PermutationalWreathProduct.conj_left_of_fixed
    (quotientEmbedding block P a) (quotientEmbedding block P e.1) i hai he,
    hac]

/-- For a displayed local normal core `B₀`, this is the literal subgroup
whose top coordinate is trivial and whose every local coordinate lies in
`B₀`. -/
abbrev degreeNineBaseCore
    (B₀ : Subgroup (LocalQuotient block P)) [B₀.Normal] :
    Subgroup (preE7NonPairAction w U ⧸ E block P) :=
  PermutationalWreathProduct.Compression.kernel
    (quotientEmbedding block P) (QuotientGroup.mk' B₀)

/-- The displayed local-core subgroup always lies in the literal linear
block kernel. -/
theorem degreeNineBaseCore_le_linearBlockKernel
    (B₀ : Subgroup (LocalQuotient block P)) [B₀.Normal] :
    degreeNineBaseCore block P B₀ ≤ degreeNineLinearBlockKernel block P := by
  intro x hx
  apply MonoidHom.mem_ker.mpr
  exact (PermutationalWreathProduct.mem_mapBase_ker_iff
    (QuotientGroup.mk' B₀) (quotientEmbedding block P x)).mp hx |>.1

/-- If every coordinate range of the actual linear kernel lies in `B₀`,
then the linear kernel is exactly the displayed local-core subgroup. -/
theorem degreeNineLinearBlockKernel_le_baseCore
    (B₀ : Subgroup (LocalQuotient block P)) [B₀.Normal]
    (hcoordinate : ∀ i : block.Points,
      (degreeNineLinearBlockKernelCoordinate block P i).range ≤ B₀) :
    degreeNineLinearBlockKernel block P ≤ degreeNineBaseCore block P B₀ := by
  intro x hx
  apply (PermutationalWreathProduct.mem_mapBase_ker_iff
    (QuotientGroup.mk' B₀) (quotientEmbedding block P x)).mpr
  refine ⟨MonoidHom.mem_ker.mp hx, ?_⟩
  intro i
  have hmem : degreeNineLinearBlockKernelCoordinate block P i ⟨x, hx⟩ ∈
      (degreeNineLinearBlockKernelCoordinate block P i).range :=
    ⟨⟨x, hx⟩, rfl⟩
  simpa only [QuotientGroup.ker_mk'] using hcoordinate i hmem

/-- In particular, vanishing of the displayed base core forces vanishing of
the whole linear kernel as soon as the local normal ranges lie in `B₀`.
This is the exact generic part of the manuscript's zero-core transition
`D = 1 ⇒ K = 1`; the seven-local table supplies `hcoordinate`. -/
theorem degreeNineLinearBlockKernel_eq_bot_of_baseCore_eq_bot
    (B₀ : Subgroup (LocalQuotient block P)) [B₀.Normal]
    (hcoordinate : ∀ i : block.Points,
      (degreeNineLinearBlockKernelCoordinate block P i).range ≤ B₀)
    (hcore : degreeNineBaseCore block P B₀ = ⊥) :
    degreeNineLinearBlockKernel block P = ⊥ := by
  apply le_bot_iff.mp
  exact (degreeNineLinearBlockKernel_le_baseCore block P B₀ hcoordinate).trans
    (le_of_eq hcore)

/-! ## Pairing disjoint ambient types -/

/-- Translation-nontrivial and outer ambient types share character slots
whenever their literal socle sums have no common ambient normal quotient. -/
theorem degreeNine_socle_normalGen_le_max_translation_outer
    (N : LiteralNormalAxis (preE7NonPairAction w U))
    (hNoCommon : NoCommonNormalQuotient
      (degreeNineTranslationSoclePart block P N)
      (degreeNineOuterSoclePart block P N)) :
    MarkedC4.normalGen
        (finiteGroupSocle (preE7NonPairAction w U ⧸ N.1)) ≤
      max
        (MarkedC4.normalGen (degreeNineTranslationSoclePart block P N))
        (MarkedC4.normalGen (degreeNineOuterSoclePart block P N)) := by
  rw [← degreeNineTranslation_outer_socle_sup block P N]
  exact normalGen_sup_le_max_of_noCommonNormalQuotient _ _ hNoCommon

/-- In the nonzero-core branch, separate `s`-slot estimates on the two
disjoint action-type sums give the required `s`-slot whole-socle tuple. -/
theorem degreeNineNonzeroCore_socleGenerators_of_typeSharing
    (N : LiteralNormalAxis (preE7NonPairAction w U))
    (hNoCommon : NoCommonNormalQuotient
      (degreeNineTranslationSoclePart block P N)
      (degreeNineOuterSoclePart block P N))
    (htranslation :
      MarkedC4.normalGen (degreeNineTranslationSoclePart block P N) ≤
        Nat.card block.Points)
    (houter :
      MarkedC4.normalGen (degreeNineOuterSoclePart block P N) ≤
        Nat.card block.Points) :
    SocleNormalGeneratorBound
      (preE7NonPairAction w U ⧸ N.1) (Nat.card block.Points) := by
  apply (socleNormalGeneratorBound_iff_normalGen_le _ _).2
  exact (degreeNine_socle_normalGen_le_max_translation_outer
    block P N hNoCommon).trans (max_le htranslation houter)

/-- The complete nonzero-core generator bound in the form used by the
degree-nine structural table.  The translation contribution is discharged
from the literal `9^s` coordinate bound and the sizes of the ambient minimal
normal factors which it contains.  Thus the only remaining action statements
are the outer-type row and the precise no-common-quotient condition which
allows the two tuples to be paired. -/
theorem degreeNineNonzeroCore_socleGenerators_of_ambientSections
    (hr : Nat.card block.Fibre = 9)
    (N : LiteralNormalAxis (preE7NonPairAction w U))
    (hmin : ∀ M : Subgroup (preE7NonPairAction w U ⧸ N.1),
      IsMinimalNormalSubgroup M →
      M ≤ degreeNineTranslationImage block P N →
      9 ≤ Nat.card M)
    (hNoCommon : NoCommonNormalQuotient
      (degreeNineTranslationSoclePart block P N)
      (degreeNineOuterSoclePart block P N))
    (houter :
      MarkedC4.normalGen (degreeNineOuterSoclePart block P N) ≤
        Nat.card block.Points) :
    SocleNormalGeneratorBound
      (preE7NonPairAction w U ⧸ N.1) (Nat.card block.Points) :=
  degreeNineNonzeroCore_socleGenerators_of_typeSharing block P N hNoCommon
    (degreeNineTranslationSoclePart_normalGen_le block P hr N hmin) houter

/-- Uniform retained-axis form of the nonzero-core theorem.  This is the
exact function consumed by `degreeNineNonzeroCoreInterval`; no quotient is
replaced by an abstract group and the retained condition is available to
each action-specific premise. -/
theorem degreeNineNonzeroCore_allNormalAxes
    (hr : Nat.card block.Fibre = 9)
    (hmin : ∀ (N : LiteralNormalAxis (preE7NonPairAction w U)),
      ¬ E block P ≤ N.1 →
      ∀ M : Subgroup (preE7NonPairAction w U ⧸ N.1),
        IsMinimalNormalSubgroup M →
        M ≤ degreeNineTranslationImage block P N →
        9 ≤ Nat.card M)
    (hNoCommon : ∀ (N : LiteralNormalAxis (preE7NonPairAction w U)),
      ¬ E block P ≤ N.1 →
      NoCommonNormalQuotient
        (degreeNineTranslationSoclePart block P N)
        (degreeNineOuterSoclePart block P N))
    (houter : ∀ (N : LiteralNormalAxis (preE7NonPairAction w U)),
      ¬ E block P ≤ N.1 →
      MarkedC4.normalGen (degreeNineOuterSoclePart block P N) ≤
        Nat.card block.Points) :
    ∀ N : LiteralNormalAxis (preE7NonPairAction w U),
      ¬ E block P ≤ N.1 →
      SocleNormalGeneratorBound
        (preE7NonPairAction w U ⧸ N.1) (Nat.card block.Points) := by
  intro N hretained
  exact degreeNineNonzeroCore_socleGenerators_of_ambientSections block P hr N
    (hmin N hretained) (hNoCommon N hretained) (houter N hretained)

/-- Ternary and nonternary ambient types likewise share slots under their
literal no-common-normal-quotient condition. -/
theorem degreeNine_socle_normalGen_le_max_ternary_nonTernary
    (N : LiteralNormalAxis (preE7NonPairAction w U))
    (hNoCommon : NoCommonNormalQuotient
      (degreeNineTernarySoclePart N)
      (degreeNineNonTernarySoclePart N)) :
    MarkedC4.normalGen
        (finiteGroupSocle (preE7NonPairAction w U ⧸ N.1)) ≤
      max
        (MarkedC4.normalGen (degreeNineTernarySoclePart N))
        (MarkedC4.normalGen (degreeNineNonTernarySoclePart N)) := by
  rw [← degreeNineTernary_nonTernary_socle_sup N]
  exact normalGen_sup_le_max_of_noCommonNormalQuotient _ _ hNoCommon

/-- In the zero-core branch, only the ternary filtration pays the additive
`s + floor(s/3)` cost.  The nonternary type sum shares those slots by max. -/
theorem degreeNineZeroCore_socleGenerators_of_typeSharing
    (N : LiteralNormalAxis (preE7NonPairAction w U))
    (hNoCommon : NoCommonNormalQuotient
      (degreeNineTernarySoclePart N)
      (degreeNineNonTernarySoclePart N))
    (hternary :
      MarkedC4.normalGen (degreeNineTernarySoclePart N) ≤
        Nat.card block.Points + Nat.card block.Points / 3)
    (hnonTernary :
      MarkedC4.normalGen (degreeNineNonTernarySoclePart N) ≤
        Nat.card block.Points) :
    SocleNormalGeneratorBound
      (preE7NonPairAction w U ⧸ N.1)
      (Nat.card block.Points + Nat.card block.Points / 3) := by
  apply (socleNormalGeneratorBound_iff_normalGen_le _ _).2
  refine (degreeNine_socle_normalGen_le_max_ternary_nonTernary
    N hNoCommon).trans (max_le hternary ?_)
  exact hnonTernary.trans (Nat.le_add_right _ _)

/-- The complete zero-core generator bound with the manuscript's three
type-sensitive obligations exposed separately.  Only the two ternary pieces
are added: translation-carried ternary types use `s` slots and outer ternary
types use `floor(s/3)` slots.  The nonternary part shares the resulting tuple
by the no-common-normal-quotient theorem. -/
theorem degreeNineZeroCore_socleGenerators_of_typedSections
    (N : LiteralNormalAxis (preE7NonPairAction w U))
    (hNoCommon : NoCommonNormalQuotient
      (degreeNineTernarySoclePart N)
      (degreeNineNonTernarySoclePart N))
    (htranslation : MarkedC4.normalGen
      (degreeNineTernaryTranslationSoclePart block P N) ≤
        Nat.card block.Points)
    (houter : MarkedC4.normalGen
      (degreeNineTernaryOuterSoclePart block P N) ≤
        Nat.card block.Points / 3)
    (hnonTernary : MarkedC4.normalGen
      (degreeNineNonTernarySoclePart N) ≤
        Nat.card block.Points) :
    SocleNormalGeneratorBound
      (preE7NonPairAction w U ⧸ N.1)
      (Nat.card block.Points + Nat.card block.Points / 3) :=
  degreeNineZeroCore_socleGenerators_of_typeSharing block N hNoCommon
    (degreeNineTernary_normalGen_le_slots block P N htranslation houter)
    hnonTernary

/-- Uniform retained-axis form of the zero-core theorem.  It records the
three actual type rows separately and assembles the `s + floor(s/3)` tuple
only after the literal quotient has been fixed. -/
theorem degreeNineZeroCore_allNormalAxes
    (hNoCommon : ∀ (N : LiteralNormalAxis (preE7NonPairAction w U)),
      ¬ E block P ≤ N.1 →
      NoCommonNormalQuotient
        (degreeNineTernarySoclePart N)
        (degreeNineNonTernarySoclePart N))
    (htranslation : ∀ (N : LiteralNormalAxis (preE7NonPairAction w U)),
      ¬ E block P ≤ N.1 →
      MarkedC4.normalGen
        (degreeNineTernaryTranslationSoclePart block P N) ≤
          Nat.card block.Points)
    (houter : ∀ (N : LiteralNormalAxis (preE7NonPairAction w U)),
      ¬ E block P ≤ N.1 →
      MarkedC4.normalGen (degreeNineTernaryOuterSoclePart block P N) ≤
        Nat.card block.Points / 3)
    (hnonTernary : ∀ (N : LiteralNormalAxis (preE7NonPairAction w U)),
      ¬ E block P ≤ N.1 →
      MarkedC4.normalGen (degreeNineNonTernarySoclePart N) ≤
        Nat.card block.Points) :
    ∀ N : LiteralNormalAxis (preE7NonPairAction w U),
      ¬ E block P ≤ N.1 →
      SocleNormalGeneratorBound
        (preE7NonPairAction w U ⧸ N.1)
        (Nat.card block.Points + Nat.card block.Points / 3) := by
  intro N hretained
  exact degreeNineZeroCore_socleGenerators_of_typedSections block P N
    (hNoCommon N hretained) (htranslation N hretained)
    (houter N hretained) (hnonTernary N hretained)

@[simp] theorem degreeNineZeroCoreSlots_six
    (hs : Nat.card block.Points = 6) :
    degreeNineZeroCoreSlots block = 8 := by
  rw [degreeNineZeroCoreSlots]
  change Nat.card block.Points + Nat.card block.Points / 3 = 8
  omega

@[simp] theorem degreeNineZeroCoreSlots_twelve
    (hs : Nat.card block.Points = 12) :
    degreeNineZeroCoreSlots block = 16 := by
  rw [degreeNineZeroCoreSlots]
  change Nat.card block.Points + Nat.card block.Points / 3 = 16
  omega

/-- The quotient comparator attached to a local degree-nine affine block has
exactly eight points per original block. -/
theorem degreeNine_quotientDegree_eq_eight_mul
    (hr : Nat.card block.Fibre = 9) :
    quotientDegree block = 8 * Nat.card block.Points := by
  rw [quotientDegree_eq block, hr]

private theorem three_logFive_lt_seven :
    3 * Real.logb 2 5 < 7 := by
  have hp : ((5 : ℝ) ^ 3) < (2 : ℝ) ^ (7 : ℕ) := by norm_num
  have hl := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (pow_pos (by norm_num) 3) hp
  simp only [Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hl
  exact_mod_cast hl

/-- The eight-point-per-block quotient comparator has the required padded
degree margin at every exceptional degree-nine block count. -/
theorem degreeNine_comparator_margin
    (hr : Nat.card block.Fibre = 9)
    (hs : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3 ∨
      Nat.card block.Points = 4 ∨ Nat.card block.Points = 6 ∨
      Nat.card block.Points = 12) :
    preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - (max 2 (quotientDegree block) : ℕ)) / 8 := by
  have hw := width_eq block
  have hq := degreeNine_quotientDegree_eq_eight_mul block hr
  have hrF : Fintype.card block.Fibre = 9 := by
    simpa only [Nat.card_eq_fintype_card] using hr
  rcases hs with hs | hs | hs | hs | hs
  all_goals
    rw [Nat.card_eq_fintype_card] at hs
    rw [hq, Nat.card_eq_fintype_card, hs]
    norm_num [hrF, hs] at hw
    norm_num [hw, preE7CharacterRho, evenWidth, halfDegree]

/-- One character slot per block lies strictly inside the common cold
window at all five exceptional degree-nine block counts. -/
theorem degreeNine_nonzeroCore_theta_window
    (hr : Nat.card block.Fibre = 9)
    (hs : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3 ∨
      Nat.card block.Points = 4 ∨ Nat.card block.Points = 6 ∨
      Nat.card block.Points = 12) :
    (Nat.card block.Points : ℝ) * (Real.logb 2 5 / 3) ≤
      preE7CharacterWindow w := by
  have hw := width_eq block
  have hlog := three_logFive_lt_seven
  have hrF : Fintype.card block.Fibre = 9 := by
    simpa only [Nat.card_eq_fintype_card] using hr
  rcases hs with hs | hs | hs | hs | hs
  all_goals
    rw [Nat.card_eq_fintype_card] at hs
    rw [Nat.card_eq_fintype_card, hs]
    norm_num [hrF, hs] at hw
    norm_num [hw, preE7CharacterWindow, preE7CharacterRho,
      halfDegree] at hlog ⊢
    linarith

/-- The enlarged zero-core tuple also lies inside the cold window at the two
surviving block counts. -/
theorem degreeNine_zeroCore_theta_window
    (hr : Nat.card block.Fibre = 9)
    (hs : Nat.card block.Points = 6 ∨ Nat.card block.Points = 12) :
    ((Nat.card block.Points + Nat.card block.Points / 3 : ℕ) : ℝ) *
        (Real.logb 2 5 / 3) ≤ preE7CharacterWindow w := by
  have hw := width_eq block
  have hlog := three_logFive_lt_seven
  have hrF : Fintype.card block.Fibre = 9 := by
    simpa only [Nat.card_eq_fintype_card] using hr
  rcases hs with hs | hs
  all_goals
    rw [Nat.card_eq_fintype_card] at hs
    rw [Nat.card_eq_fintype_card, hs]
    norm_num [hrF, hs] at hw
    norm_num [hw, preE7CharacterWindow, preE7CharacterRho,
      halfDegree] at hlog ⊢
    linarith

/-- A direct whole-socle bound is exactly the nonzero-core degree-nine
budget.  This small lemma keeps the structural proof in `normalGen` form. -/
theorem degreeNineNonzeroCore_socleGenerators
    {Q : Type} [Group Q] [Finite Q]
    (h : MarkedC4.normalGen (finiteGroupSocle Q) ≤
      Nat.card block.Points) :
    SocleNormalGeneratorBound Q (Nat.card block.Points) :=
  (socleNormalGeneratorBound_iff_normalGen_le Q
    (Nat.card block.Points)).2 h

/-- The zero-core socle filtration.  A translation-intersection contribution
of at most `s` and a top image contribution of at most `s / 3` combine into
the manuscript's `s + floor(s/3)` slots. -/
theorem degreeNineZeroCore_socleGenerators
    {Q : Type} [Group Q] [Finite Q]
    (F : Subgroup Q) [F.Normal]
    (hinter : MarkedC4.normalGen (finiteGroupSocle Q ⊓ F) ≤
      Nat.card block.Points)
    (himage : MarkedC4.normalGen
      ((finiteGroupSocle Q).map (QuotientGroup.mk' F)) ≤
        Nat.card block.Points / 3) :
    SocleNormalGeneratorBound Q
      (Nat.card block.Points + Nat.card block.Points / 3) :=
  MarkedC4.socleNormalGeneratorBound_of_inter_image F hinter himage

/-- Package any proved uniform socle-generator estimate on the literal
quotients below the actual translation intersection.  The retained subgroup
and comparator are fixed by the original block system. -/
noncomputable def degreeNineSocleGeneratorInterval
    (slots : ℕ)
    (hgenerators : ∀ N : LiteralNormalAxis (preE7NonPairAction w U),
      ¬ E block P ≤ N.1 →
        SocleNormalGeneratorBound
          (preE7NonPairAction w U ⧸ N.1) slots) :
    SocleGeneratorCharacterIntervalData (preE7NonPairAction w U) where
  E := E block P
  quotientDegree := quotientDegree block
  quotientAction := quotientAction block P
  quotientAction_injective := quotientAction_injective block P
  slots := slots
  quotientSocleGenerators := hgenerators

/-- Degree-nine nonzero-core interval: one slot per block. -/
noncomputable def degreeNineNonzeroCoreInterval
    (hgenerators : ∀ N : LiteralNormalAxis (preE7NonPairAction w U),
      ¬ E block P ≤ N.1 →
        SocleNormalGeneratorBound (preE7NonPairAction w U ⧸ N.1)
          (Nat.card block.Points)) :
    SocleGeneratorCharacterIntervalData (preE7NonPairAction w U) :=
  degreeNineSocleGeneratorInterval block P (Nat.card block.Points) hgenerators

/-- Degree-nine zero-core interval: the translation section costs `s` slots
and the top elementary ternary section costs `s / 3` more. -/
noncomputable def degreeNineZeroCoreInterval
    (hgenerators : ∀ N : LiteralNormalAxis (preE7NonPairAction w U),
      ¬ E block P ≤ N.1 →
        SocleNormalGeneratorBound (preE7NonPairAction w U ⧸ N.1)
          (Nat.card block.Points + Nat.card block.Points / 3)) :
    SocleGeneratorCharacterIntervalData (preE7NonPairAction w U) :=
  degreeNineSocleGeneratorInterval block P
    (Nat.card block.Points + Nat.card block.Points / 3) hgenerators

/-- Install the published Zmud theorem after the structural degree-nine
normal-generator estimate has been proved. -/
noncomputable def degreeNineCompleteCharacterInterval
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (slots : ℕ)
    (hgenerators : ∀ N : LiteralNormalAxis (preE7NonPairAction w U),
      ¬ E block P ≤ N.1 →
        SocleNormalGeneratorBound
          (preE7NonPairAction w U ⧸ N.1) slots) :
    CompleteCharacterIntervalData (preE7NonPairAction w U) :=
  (degreeNineSocleGeneratorInterval block P slots hgenerators
    ).toCompleteCharacterIntervalData hZmud

/-- All non-coefficient numerics for the nonzero-core degree-nine interval.
The finite `tailConstant` is kept as a separate routine menu estimate, so
this constructor contains exactly the structural and sharp fixed-width
arithmetic proved in this file. -/
noncomputable def degreeNineNonzeroCoreCompleteCharacterNumerics
    (hr : Nat.card block.Fibre = 9)
    (hs : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3 ∨
      Nat.card block.Points = 4 ∨ Nat.card block.Points = 6 ∨
      Nat.card block.Points = 12)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (hgenerators : ∀ N : LiteralNormalAxis (preE7NonPairAction w U),
      ¬ E block P ≤ N.1 →
        SocleNormalGeneratorBound (preE7NonPairAction w U ⧸ N.1)
          (Nat.card block.Points))
    (htail : ∀ b,
      (degreeNineCompleteCharacterInterval block P hZmud
        (Nat.card block.Points) hgenerators).tailConstant ≤
        (2 : ℝ) ^
          (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)) :
    PreE7CompleteCharacterIntervalNumerics
      (degreeNineCompleteCharacterInterval block P hZmud
        (Nat.card block.Points) hgenerators) := by
  refine
    { comparator_margin := ?_
      theta_window := ?_
      tail_total_bound := htail }
  · change preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - (max 2 (quotientDegree block) : ℕ)) / 8
    exact degreeNine_comparator_margin block hr hs
  · change (Nat.card block.Points : ℝ) * (Real.logb 2 5 / 3) ≤
      preE7CharacterWindow w
    exact degreeNine_nonzeroCore_theta_window block hr hs

/-- All non-coefficient numerics for the zero-core degree-nine interval at
the two surviving block counts. -/
noncomputable def degreeNineZeroCoreCompleteCharacterNumerics
    (hr : Nat.card block.Fibre = 9)
    (hs : Nat.card block.Points = 6 ∨ Nat.card block.Points = 12)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (hgenerators : ∀ N : LiteralNormalAxis (preE7NonPairAction w U),
      ¬ E block P ≤ N.1 →
        SocleNormalGeneratorBound (preE7NonPairAction w U ⧸ N.1)
          (Nat.card block.Points + Nat.card block.Points / 3))
    (htail : ∀ b,
      (degreeNineCompleteCharacterInterval block P hZmud
        (Nat.card block.Points + Nat.card block.Points / 3)
        hgenerators).tailConstant ≤
        (2 : ℝ) ^
          (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)) :
    PreE7CompleteCharacterIntervalNumerics
      (degreeNineCompleteCharacterInterval block P hZmud
        (Nat.card block.Points + Nat.card block.Points / 3)
        hgenerators) := by
  have hs' : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3 ∨
      Nat.card block.Points = 4 ∨ Nat.card block.Points = 6 ∨
      Nat.card block.Points = 12 := by
    rcases hs with hs | hs
    · exact Or.inr (Or.inr (Or.inr (Or.inl hs)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hs)))
  refine
    { comparator_margin := ?_
      theta_window := ?_
      tail_total_bound := htail }
  · change preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - (max 2 (quotientDegree block) : ℕ)) / 8
    exact degreeNine_comparator_margin block hr hs'
  · change
      ((Nat.card block.Points + Nat.card block.Points / 3 : ℕ) : ℝ) *
          (Real.logb 2 5 / 3) ≤ preE7CharacterWindow w
    exact degreeNine_zeroCore_theta_window block hr hs

/-- Final source constructor once the elementary fixed-width numerical
certificate has been discharged.  This is only plumbing: the source is the
already-proved complete-character-interval theorem. -/
noncomputable def degreeNineCharacterIntervalSource
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (slots : ℕ)
    (hgenerators : ∀ N : LiteralNormalAxis (preE7NonPairAction w U),
      ¬ E block P ≤ N.1 →
        SocleNormalGeneratorBound
          (preE7NonPairAction w U ⧸ N.1) slots)
    (numerics : PreE7CompleteCharacterIntervalNumerics
      (degreeNineCompleteCharacterInterval block P hZmud slots hgenerators)) :
    PreE7RankTailSourceOrYonedaTopData w U :=
  numerics.toRankTailSourceOrYonedaTop lit family

/-- Counting-ready nonzero-core degree-nine source. -/
noncomputable def degreeNineNonzeroCoreCharacterIntervalSource
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (hr : Nat.card block.Fibre = 9)
    (hs : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3 ∨
      Nat.card block.Points = 4 ∨ Nat.card block.Points = 6 ∨
      Nat.card block.Points = 12)
    (hgenerators : ∀ N : LiteralNormalAxis (preE7NonPairAction w U),
      ¬ E block P ≤ N.1 →
        SocleNormalGeneratorBound (preE7NonPairAction w U ⧸ N.1)
          (Nat.card block.Points))
    (htail : ∀ b,
      (degreeNineCompleteCharacterInterval block P hZmud
        (Nat.card block.Points) hgenerators).tailConstant ≤
        (2 : ℝ) ^
          (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)) :
    PreE7RankTailSourceOrYonedaTopData w U :=
  (degreeNineNonzeroCoreCompleteCharacterNumerics block P hr hs hZmud
      hgenerators htail).toRankTailSourceOrYonedaTop lit family

/-- Counting-ready zero-core degree-nine source. -/
noncomputable def degreeNineZeroCoreCharacterIntervalSource
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (hr : Nat.card block.Fibre = 9)
    (hs : Nat.card block.Points = 6 ∨ Nat.card block.Points = 12)
    (hgenerators : ∀ N : LiteralNormalAxis (preE7NonPairAction w U),
      ¬ E block P ≤ N.1 →
        SocleNormalGeneratorBound (preE7NonPairAction w U ⧸ N.1)
          (Nat.card block.Points + Nat.card block.Points / 3))
    (htail : ∀ b,
      (degreeNineCompleteCharacterInterval block P hZmud
        (Nat.card block.Points + Nat.card block.Points / 3)
        hgenerators).tailConstant ≤
        (2 : ℝ) ^
          (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)) :
    PreE7RankTailSourceOrYonedaTopData w U :=
  (degreeNineZeroCoreCompleteCharacterNumerics block P hr hs hZmud
      hgenerators htail).toRankTailSourceOrYonedaTop lit family

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu

end SymmetricSubgroupAsymptotics

end
