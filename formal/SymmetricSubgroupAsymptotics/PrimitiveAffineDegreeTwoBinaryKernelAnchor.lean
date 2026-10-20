import SymmetricSubgroupAsymptotics.BinaryCharacterEnvelope
import SymmetricSubgroupAsymptotics.FusionEpimorphismTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairRelativeAnchorLabels

/-!
# Binary-kernel anchors for the degree-two pair lift

The paper's relative-pair argument starts with a fixed character prefix whose
joint kernel is a binary group.  Equal prefix labels determine the same
preimage of that binary kernel.  On that preimage the original epimorphism is
an epimorphism onto the fixed binary kernel, so the already formalized
Maróti/Sylow character bound applies to the preimage through its faithful
permutation action.

This file packages that argument directly.  It constructs the dependent
prefix/preimage label and proves the complete-source epimorphism envelope;
callers supply actual prefix characters and the finite binary-kernel rank
bound, rather than a hand-built relative label on every later source.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- The original-source binary envelope only needs a faithful action of the
source on `b` points.  This form is used for an anchor preimage, which is a
subgroup of the complete permutation source rather than a subgroup of the
ambient symmetric group definitionally. -/
theorem binary_groupEpimorphism_faithfulPermutation_envelope
    (hMaroti : NilpotentConjugacyClassInput)
    {M Q : Type} [Group M] [Group Q] [Finite M] [Finite Q]
    (hQ : IsPGroup 2 Q) (b : ℕ)
    (action : M →* Equiv.Perm (Fin b))
    (action_injective : Function.Injective action) :
    (Nat.card (GroupEpimorphism M Q) : ℝ) ≤
      (Nat.card (Q ≃* Q) : ℝ) *
        (2 : ℝ) ^ (binaryCharacterSlope
          (Module.finrank (ZMod 2) (Additive (binaryCentralOmega Q))) *
            (b : ℝ)) := by
  let T : Subgroup (Equiv.Perm (Fin b)) := action.range
  have hinjective : Function.Injective action.rangeRestrict :=
    MonoidHom.rangeRestrict_injective_iff.mpr action_injective
  let e : M ≃* T :=
    MulEquiv.ofBijective action.rangeRestrict
      ⟨hinjective, action.rangeRestrict_surjective⟩
  rw [fusionGroupEpimorphism_card_congr e (MulEquiv.refl Q)]
  exact binary_groupEpimorphism_original_envelope hMaroti hQ b T

/-- A fixed prefix on one target quotient.  Its common kernel is literally a
binary group, and its binary central omega dimension is bounded by the
relative part of the profile. -/
structure DegreeTwoPairBinaryKernelAnchor
    (Q : Type) [Group Q] [Finite Q]
    (profile : DegreeTwoPairRelativeProfile) : Type 1 where
  binary : Fin profile.binaryPrimary → Q →* ℂˣ
  binary_twoGroup : ∀ i, IsPGroup 2 (binary i).range
  linear : Fin profile.linear → Q →* ℂˣ
  ordinary : Fin profile.ordinary → FiniteIrreducibleRepresentation ℂ Q
  kernel : Subgroup Q
  [kernel_normal : kernel.Normal]
  kernel_eq : kernel =
    ((⨅ i, (binary i).ker) ⊓ (⨅ i, (linear i).ker)) ⊓
      (⨅ i, (ordinary i).action.ker)
  kernel_twoGroup : IsPGroup 2 kernel
  relative_dimension :
    Module.finrank (ZMod 2) (Additive (binaryCentralOmega kernel)) ≤
      profile.relative

/-- The pure ordinary profile supplied by a `t`-generator socle theorem. -/
def degreeTwoPairGeneralProfile (t : ℕ) : DegreeTwoPairRelativeProfile where
  binaryPrimary := 0
  linear := 0
  ordinary := t
  relative := 0

/-- The profile supplied by a faithful ordinary prefix on a quotient whose
common kernel is binary.  The ordinary positions see the quotient by that
kernel; the relative positions pay only for the binary kernel itself. -/
def degreeTwoPairOrdinaryRelativeProfile
    (ordinary relative : ℕ) : DegreeTwoPairRelativeProfile where
  binaryPrimary := 0
  linear := 0
  ordinary := ordinary
  relative := relative

attribute [instance] DegreeTwoPairBinaryKernelAnchor.kernel_normal

namespace DegreeTwoPairBinaryKernelAnchor

variable {Q : Type} [Group Q] [Finite Q]
  {profile : DegreeTwoPairRelativeProfile}
  (A : DegreeTwoPairBinaryKernelAnchor Q profile)

/-- A Zmud tuple which is jointly faithful on the whole quotient is the
degenerate binary-kernel anchor with common kernel `⊥`.  This turns a
finite socle-generator certificate directly into pair-row data and avoids
manufacturing a source-dependent relative label. -/
noncomputable def ofSocleGeneratorBound
    (hZmud : ZmudFaithfulCharacterTupleInput) {t : ℕ}
    (hgen : SocleNormalGeneratorBound Q t) :
    DegreeTwoPairBinaryKernelAnchor Q (degreeTwoPairGeneralProfile t) := by
  let T : CharacterSlotTuple Q := hZmud.generalTuple hgen
  exact
    { binary := Fin.elim0
      binary_twoGroup := fun i ↦ Fin.elim0 i
      linear := Fin.elim0
      ordinary := T.general
      kernel := ⊥
      kernel_eq := by
        symm
        apply bot_unique
        intro q hq
        simp only [Subgroup.mem_inf, Subgroup.mem_iInf,
          MonoidHom.mem_ker] at hq
        exact Subgroup.mem_bot.mpr
          (T.faithful q (fun i ↦ Fin.elim0 i)
            (fun i ↦ Fin.elim0 i) hq.2)
      kernel_twoGroup := IsPGroup.of_bot
      relative_dimension := by
        simp only [Module.finrank_zero_of_subsingleton]
        exact Nat.zero_le _ }

/-- Inflate a Zmud tuple through an arbitrary surjective quotient with
binary kernel.  The inflated constituents have common kernel exactly
`π.ker`, so the ordinary prefix and the binary relative tail form a
`DegreeTwoPairBinaryKernelAnchor`.

This is the reusable semantic bridge needed by the pair-top catalogues: a
finite top registry supplies the socle generators of the quotient, while a
finite invariant-module registry supplies the relative binary rank. -/
noncomputable def ofSurjectiveBinaryKernel
    {B : Type} [Group B] [Finite B]
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (π : Q →* B) (hπ : Function.Surjective π)
    {ordinary relative : ℕ}
    (hgen : SocleNormalGeneratorBound B ordinary)
    (hker : IsPGroup 2 π.ker)
    (hrank :
      Module.finrank (ZMod 2) (Additive (binaryCentralOmega π.ker)) ≤
        relative) :
    DegreeTwoPairBinaryKernelAnchor Q
      (degreeTwoPairOrdinaryRelativeProfile ordinary relative) := by
  let rho : Fin ordinary → FiniteIrreducibleRepresentation ℂ B :=
    Classical.choose (hZmud B ordinary hgen)
  have hrho : ∀ b : B, (∀ i, (rho i).action b = 1) → b = 1 :=
    Classical.choose_spec (hZmud B ordinary hgen)
  let inflated : Fin ordinary → FiniteIrreducibleRepresentation ℂ Q :=
    fun i ↦
      { Space := (rho i).Space
        addCommGroup := inferInstance
        module := inferInstance
        finiteDimensional := inferInstance
        action := (rho i).action.comp π
        irreducible := representation_irreducible_comp
          (rho i).action π hπ }
  exact
    { binary := Fin.elim0
      binary_twoGroup := fun i ↦ Fin.elim0 i
      linear := Fin.elim0
      ordinary := inflated
      kernel := π.ker
      kernel_eq := by
        ext q
        simp only [Subgroup.mem_inf, Subgroup.mem_iInf,
          MonoidHom.mem_ker]
        constructor
        · intro hq
          refine ⟨⟨fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i⟩, ?_⟩
          intro i
          change (rho i).action (π q) = 1
          rw [hq, map_one]
        · rintro ⟨⟨_, _⟩, hord⟩
          apply hrho
          intro i
          simpa only [inflated, MonoidHom.comp_apply] using hord i
      kernel_twoGroup := hker
      relative_dimension := hrank }

private def PrefixLabel (J : Type) [Group J] [Finite J]
    [Invertible (Nat.card J : ℂ)] : Type :=
  (∀ i, linearCharacterLabels (J := J) (A.binary i)) ×
    (∀ i, linearCharacterLabels (J := J) (A.linear i)) ×
    (∀ i, epimorphismCharacterLabels (J := J) (A.ordinary i).action)

private def prefixLabel {J : Type} [Group J] [Finite J]
    [Invertible (Nat.card J : ℂ)]
    (f : GroupEpimorphism J Q) : A.PrefixLabel J :=
  (fun i ↦ ⟨(A.binary i).comp f.1, f, rfl⟩,
    fun i ↦ ⟨(A.linear i).comp f.1, f, rfl⟩,
    fun i ↦ ⟨Representation.character
      ((A.ordinary i).action.comp f.1), f, rfl⟩)

/-- Equal fixed-prefix labels give exactly the same source preimage of the
binary anchor kernel. -/
private theorem kernel_comap_eq_of_prefixLabel_eq
    {J : Type} [Group J] [Finite J]
    [Invertible (Nat.card J : ℂ)]
    (f g : GroupEpimorphism J Q)
    (h : A.prefixLabel f = A.prefixLabel g) :
    A.kernel.comap f.1 = A.kernel.comap g.1 := by
  obtain ⟨hb, hl, ho⟩ := Prod.ext_iff.mp h |>.imp id Prod.ext_iff.mp
  rw [A.kernel_eq]
  ext x
  simp only [Subgroup.mem_comap, Subgroup.mem_inf, Subgroup.mem_iInf,
    MonoidHom.mem_ker, MonoidHom.comp_apply]
  constructor
  · rintro ⟨⟨hbin, hlin⟩, hord⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i
      have hi := congrArg Subtype.val (congrFun hb i)
      exact DFunLike.congr_fun hi x ▸ hbin i
    · intro i
      have hi := congrArg Subtype.val (congrFun hl i)
      exact DFunLike.congr_fun hi x ▸ hlin i
    · intro i
      have hi := representation_comp_ker_eq_of_character_eq
        (A.ordinary i) f g (congrArg Subtype.val (congrFun ho i))
      have hx : x ∈ ((A.ordinary i).action.comp f.1).ker := by
        simpa only [MonoidHom.mem_ker, MonoidHom.comp_apply] using hord i
      rw [hi] at hx
      simpa only [MonoidHom.mem_ker, MonoidHom.comp_apply] using hx
  · rintro ⟨⟨hbin, hlin⟩, hord⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i
      have hi := congrArg Subtype.val (congrFun hb i)
      exact (DFunLike.congr_fun hi x).symm ▸ hbin i
    · intro i
      have hi := congrArg Subtype.val (congrFun hl i)
      exact (DFunLike.congr_fun hi x).symm ▸ hlin i
    · intro i
      have hi := representation_comp_ker_eq_of_character_eq
        (A.ordinary i) f g (congrArg Subtype.val (congrFun ho i))
      have hx : x ∈ ((A.ordinary i).action.comp g.1).ker := by
        simpa only [MonoidHom.mem_ker, MonoidHom.comp_apply] using hord i
      rw [← hi] at hx
      simpa only [MonoidHom.mem_ker, MonoidHom.comp_apply] using hx

private def AnchorLabel {J : Type} [Group J] [Finite J]
    [Invertible (Nat.card J : ℂ)] : Type :=
  Set.range (A.prefixLabel (J := J))

private noncomputable def anchorRepresentative
    {J : Type} [Group J] [Finite J]
    [Invertible (Nat.card J : ℂ)]
    (a : A.AnchorLabel (J := J)) : GroupEpimorphism J Q :=
  Classical.choose a.2

private theorem anchorRepresentative_spec
    {J : Type} [Group J] [Finite J]
    [Invertible (Nat.card J : ℂ)]
    (a : A.AnchorLabel (J := J)) :
    A.prefixLabel (A.anchorRepresentative a) = a.1 :=
  Classical.choose_spec a.2

private def anchorLabel {J : Type} [Group J] [Finite J]
    [Invertible (Nat.card J : ℂ)]
    (f : GroupEpimorphism J Q) : A.AnchorLabel (J := J) :=
  ⟨A.prefixLabel f, f, rfl⟩

private def anchorSource {J : Type} [Group J] [Finite J]
    [Invertible (Nat.card J : ℂ)]
    (a : A.AnchorLabel (J := J)) : Subgroup J :=
  A.kernel.comap (A.anchorRepresentative a).1

private theorem anchorSource_anchorLabel
    {J : Type} [Group J] [Finite J]
    [Invertible (Nat.card J : ℂ)]
    (f : GroupEpimorphism J Q) :
    A.anchorSource (A.anchorLabel f) = A.kernel.comap f.1 := by
  apply A.kernel_comap_eq_of_prefixLabel_eq
  exact (A.anchorRepresentative_spec (A.anchorLabel f)).trans rfl

/-- Restrict an onto map to the source preimage selected by its prefix and
codrestrict it to the fixed binary kernel. -/
private noncomputable def anchorRestriction
    {J : Type} [Group J] [Finite J]
    [Invertible (Nat.card J : ℂ)]
    (f : GroupEpimorphism J Q) :
    GroupEpimorphism (A.anchorSource (A.anchorLabel f)) A.kernel := by
  let M := A.anchorSource (A.anchorLabel f)
  let map : M →* A.kernel :=
    { toFun := fun x ↦ ⟨f.1 x.1, by
        have hx : x.1 ∈ A.kernel.comap f.1 := by
          rw [← A.anchorSource_anchorLabel f]
          exact x.2
        exact hx⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by intro x y; apply Subtype.ext; simp }
  refine ⟨map, ?_⟩
  rintro ⟨q, hq⟩
  obtain ⟨x, rfl⟩ := f.2 q
  have hx : x ∈ M := by
    change x ∈ A.anchorSource (A.anchorLabel f)
    rw [A.anchorSource_anchorLabel f]
    exact hq
  exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩

private theorem anchorRestriction_kernel_comap
    {J : Type} [Group J] [Finite J]
    [Invertible (Nat.card J : ℂ)]
    (f : GroupEpimorphism J Q) :
    (A.anchorRestriction f).1.ker.map
        (A.anchorSource (A.anchorLabel f)).subtype = f.1.ker := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : (A.anchorRestriction f).1 y = 1 :=
      (MonoidHom.mem_ker).mp hy
    have hy'' := congrArg Subtype.val hy'
    change f.1 y.1 = 1 at hy''
    exact hy''
  · intro hx
    have hxM : x ∈ A.anchorSource (A.anchorLabel f) := by
      rw [A.anchorSource_anchorLabel f]
      change f.1 x ∈ A.kernel
      rw [show f.1 x = 1 from hx]
      exact A.kernel.one_mem
    refine ⟨⟨x, hxM⟩, ?_, rfl⟩
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    change f.1 x = 1
    exact hx

private theorem product_card_le_two_rpow {n : ℕ}
    (c : Fin n → ℕ) (s : ℝ) (b : ℕ)
    (hc : ∀ i, (c i : ℝ) ≤ (2 : ℝ) ^ (s * b)) :
    ((∏ i, c i : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (((n : ℝ) * s) * b) := by
  push_cast
  calc
    ∏ i, (c i : ℝ) ≤ ∏ _i : Fin n, (2 : ℝ) ^ (s * b) :=
      Finset.prod_le_prod (fun i _ ↦ Nat.cast_nonneg _) (fun i _ ↦ hc i)
    _ = ((2 : ℝ) ^ (s * b)) ^ n := by simp
    _ = (2 : ℝ) ^ (((n : ℝ) * s) * b) := by
      rw [← Real.rpow_mul_natCast (by norm_num)]
      ring_nf

private theorem three_rpow_mul (a b c : ℝ) :
    (2 : ℝ) ^ a * (2 : ℝ) ^ b * (2 : ℝ) ^ c =
      (2 : ℝ) ^ (a + b + c) := by
  rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]

/-- A binary-kernel prefix produces the exact pair-relative quotient
envelope.  The only target-dependent extra constant is the automorphism
count of the fixed binary kernel. -/
noncomputable def toQuotientEnvelope
    (lit : PreE7CharacterLiterature) :
    DegreeTwoPairRelativeQuotientEnvelope Q profile where
  coefficient :=
    (Nat.card (Q ≃* Q) : ℝ) * (Nat.card (A.kernel ≃* A.kernel) : ℝ)
  coefficient_nonneg := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  bound := by
    intro b J
    letI : Invertible (Nat.card J : ℂ) :=
      invertibleOfNonzero (by exact_mod_cast (Nat.card_pos (α := J)).ne')
    letI : Finite (A.PrefixLabel J) := by
      unfold PrefixLabel
      infer_instance
    letI : Finite (A.AnchorLabel (J := J)) :=
      Finite.of_surjective (A.anchorLabel (J := J)) (by
        rintro ⟨a, f, hf⟩
        exact ⟨f, Subtype.ext hf⟩)
    let Label := Σ a : A.AnchorLabel (J := J),
      GroupEpimorphism (A.anchorSource a) A.kernel
    let label : GroupEpimorphism J Q → Label := fun f ↦
      ⟨A.anchorLabel f, A.anchorRestriction f⟩
    let labelKernel : Label → Subgroup J := fun d ↦
      d.2.1.ker.map (A.anchorSource d.1).subtype
    have hkernel : ∀ f g, label f = label g → f.1.ker = g.1.ker := by
      intro f g h
      calc
        f.1.ker = labelKernel (label f) := by
          simpa only [labelKernel, label] using
            (A.anchorRestriction_kernel_comap f).symm
        _ = labelKernel (label g) := congrArg labelKernel h
        _ = g.1.ker := by
          simpa only [labelKernel, label] using
            A.anchorRestriction_kernel_comap g
    have hraw := groupEpimorphism_card_le_kernel_labels label hkernel
    have hrelative : ∀ a : A.AnchorLabel (J := J),
        (Nat.card (GroupEpimorphism (A.anchorSource a) A.kernel) : ℝ) ≤
          (Nat.card (A.kernel ≃* A.kernel) : ℝ) *
            (2 : ℝ) ^ (((profile.relative : ℝ) *
              Real.logb 2 (38 / 25)) * b) := by
      intro a
      let action : A.anchorSource a →* Equiv.Perm (Fin b) :=
        J.subtype.comp (A.anchorSource a).subtype
      have hinjective : Function.Injective action := by
        intro x y h
        exact Subtype.ext (Subtype.ext h)
      have h := binary_groupEpimorphism_faithfulPermutation_envelope
        lit.maroti A.kernel_twoGroup b action hinjective
      refine h.trans ?_
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hdim :
          (Module.finrank (ZMod 2)
            (Additive (binaryCentralOmega A.kernel)) : ℝ) ≤
            profile.relative := by
        exact_mod_cast A.relative_dimension
      unfold binaryCharacterSlope
      have hlog : 0 ≤ Real.logb 2 ((38 : ℝ) / 25) :=
        Real.logb_nonneg (by norm_num) (by norm_num)
      have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hdim hlog) hb
    have hbin : ((∏ i, Nat.card
        (linearCharacterLabels (J := J) (A.binary i)) : ℕ) : ℝ) ≤
        (2 : ℝ) ^ (((profile.binaryPrimary : ℝ) * (1 / 2)) * b) := by
      apply product_card_le_two_rpow
      intro i
      have h := binaryLinearCharacterSet_card_le
        lit.kovacsPraegerBinary b J
        (linearCharacterLabels (J := J) (A.binary i))
        (linearCharacterLabels_twoGroup _ (A.binary_twoGroup i))
      refine h.trans_eq ?_
      congr 1
      ring
    have hlinear : ((∏ i, Nat.card
        (linearCharacterLabels (J := J) (A.linear i)) : ℕ) : ℝ) ≤
        (2 : ℝ) ^ (((profile.linear : ℝ) *
          (Real.logb 2 3 / 3)) * b) := by
      apply product_card_le_two_rpow
      intro i
      have h1 := linearCharacterSet_card_le_abelianization
        (linearCharacterLabels (J := J) (A.linear i))
      have h2 := lit.kovacsPraeger b J
      calc
        (Nat.card (linearCharacterLabels (J := J) (A.linear i)) : ℝ) ≤
            Nat.card (Abelianization J) := by exact_mod_cast h1
        _ ≤ (3 : ℝ) ^ ((b : ℝ) / 3) := h2
        _ = (2 : ℝ) ^ ((Real.logb 2 3 / 3) * b) := by
          rw [show (3 : ℝ) ^ ((b : ℝ) / 3) =
            (2 : ℝ) ^ (Real.logb 2 3 * ((b : ℝ) / 3)) by
              rw [Real.rpow_mul (by norm_num),
                Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)]]
          congr 1
          ring
    have hordinary : ((∏ i, Nat.card (epimorphismCharacterLabels
        (J := J) (A.ordinary i).action) : ℕ) : ℝ) ≤
        (2 : ℝ) ^ (((profile.ordinary : ℝ) *
          (Real.logb 2 5 / 3)) * b) := by
      apply product_card_le_two_rpow
      intro i
      have h1 := epimorphismCharacterLabels_card
        (J := J) (A.ordinary i).action
      have h2 := conjClasses_card_le_five_rpow lit.garonziMaroti b J
      calc
        (Nat.card (epimorphismCharacterLabels
            (J := J) (A.ordinary i).action) : ℝ) ≤
            Nat.card (ConjClasses J) := by exact_mod_cast h1
        _ ≤ (5 : ℝ) ^ ((b : ℝ) / 3) := h2
        _ = (2 : ℝ) ^ ((Real.logb 2 5 / 3) * b) := by
          rw [show (5 : ℝ) ^ ((b : ℝ) / 3) =
            (2 : ℝ) ^ (Real.logb 2 5 * ((b : ℝ) / 3)) by
              rw [Real.rpow_mul (by norm_num),
                Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)]]
          congr 1
          ring
    have hanchor : (Nat.card (A.AnchorLabel (J := J)) : ℝ) ≤
        (2 : ℝ) ^ ((((profile.binaryPrimary : ℝ) * (1 / 2) +
          (profile.linear : ℝ) * (Real.logb 2 3 / 3) +
          (profile.ordinary : ℝ) * (Real.logb 2 5 / 3)) * b)) := by
      have hrange : Nat.card (A.AnchorLabel (J := J)) ≤
          Nat.card (A.PrefixLabel J) :=
        Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
      have hcast : (Nat.card (A.AnchorLabel (J := J)) : ℝ) ≤
          (Nat.card (A.PrefixLabel J) : ℝ) := by exact_mod_cast hrange
      refine hcast.trans ?_
      have hbin' : (Nat.card (∀ i,
          linearCharacterLabels (J := J) (A.binary i)) : ℝ) ≤
          (2 : ℝ) ^ (((profile.binaryPrimary : ℝ) * (1 / 2)) * b) := by
        rw [Nat.card_pi]
        exact hbin
      have hlinear' : (Nat.card (∀ i,
          linearCharacterLabels (J := J) (A.linear i)) : ℝ) ≤
          (2 : ℝ) ^ (((profile.linear : ℝ) *
            (Real.logb 2 3 / 3)) * b) := by
        rw [Nat.card_pi]
        exact hlinear
      have hordinary' : (Nat.card (∀ i,
          epimorphismCharacterLabels (J := J)
            (A.ordinary i).action) : ℝ) ≤
          (2 : ℝ) ^ (((profile.ordinary : ℝ) *
            (Real.logb 2 5 / 3)) * b) := by
        rw [Nat.card_pi]
        exact hordinary
      simp only [PrefixLabel, Nat.card_prod]
      push_cast
      calc
        (Nat.card (∀ i, linearCharacterLabels (J := J) (A.binary i)) : ℝ) *
              ((Nat.card (∀ i,
                linearCharacterLabels (J := J) (A.linear i)) : ℝ) *
                (Nat.card (∀ i, epimorphismCharacterLabels
                  (J := J) (A.ordinary i).action) : ℝ)) ≤
            (2 : ℝ) ^ (((profile.binaryPrimary : ℝ) * (1 / 2)) * b) *
              ((2 : ℝ) ^ (((profile.linear : ℝ) *
                (Real.logb 2 3 / 3)) * b) *
                (2 : ℝ) ^ (((profile.ordinary : ℝ) *
                  (Real.logb 2 5 / 3)) * b)) := by
            exact mul_le_mul hbin'
              (mul_le_mul hlinear' hordinary'
                (Nat.cast_nonneg _) (Real.rpow_nonneg (by norm_num) _))
              (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
              (Real.rpow_nonneg (by norm_num) _)
        _ = _ := by
          rw [show
            (2 : ℝ) ^ (((profile.binaryPrimary : ℝ) * (1 / 2)) * b) *
                ((2 : ℝ) ^ (((profile.linear : ℝ) *
                  (Real.logb 2 3 / 3)) * b) *
                  (2 : ℝ) ^ (((profile.ordinary : ℝ) *
                    (Real.logb 2 5 / 3)) * b)) =
              (2 : ℝ) ^ (((profile.binaryPrimary : ℝ) * (1 / 2)) * b) *
                (2 : ℝ) ^ (((profile.linear : ℝ) *
                  (Real.logb 2 3 / 3)) * b) *
                (2 : ℝ) ^ (((profile.ordinary : ℝ) *
                  (Real.logb 2 5 / 3)) * b) by ring]
          rw [three_rpow_mul]
          congr 2
          ring
    have hlabel : (Nat.card Label : ℝ) ≤
        ((Nat.card (A.kernel ≃* A.kernel) : ℝ) *
          (2 : ℝ) ^ (profile.slope * b)) := by
      letI : Fintype (A.AnchorLabel (J := J)) := Fintype.ofFinite _
      change (Nat.card (Σ a : A.AnchorLabel (J := J),
        GroupEpimorphism (A.anchorSource a) A.kernel) : ℝ) ≤ _
      rw [Nat.card_sigma, Nat.cast_sum]
      calc
        ∑ a : A.AnchorLabel (J := J),
            (Nat.card (GroupEpimorphism (A.anchorSource a) A.kernel) : ℝ) ≤
          ∑ _a : A.AnchorLabel (J := J),
            (Nat.card (A.kernel ≃* A.kernel) : ℝ) *
              (2 : ℝ) ^ (((profile.relative : ℝ) *
                Real.logb 2 (38 / 25)) * b) :=
          Finset.sum_le_sum (fun a _ ↦ hrelative a)
        _ = (Nat.card (A.AnchorLabel (J := J)) : ℝ) *
            ((Nat.card (A.kernel ≃* A.kernel) : ℝ) *
              (2 : ℝ) ^ (((profile.relative : ℝ) *
                Real.logb 2 (38 / 25)) * b)) := by
          simp only [Finset.sum_const, Finset.card_univ,
            Fintype.card_eq_nat_card, nsmul_eq_mul]
        _ ≤ (2 : ℝ) ^ (((profile.binaryPrimary : ℝ) * (1 / 2) +
              (profile.linear : ℝ) * (Real.logb 2 3 / 3) +
              (profile.ordinary : ℝ) * (Real.logb 2 5 / 3)) * b) *
            ((Nat.card (A.kernel ≃* A.kernel) : ℝ) *
              (2 : ℝ) ^ (((profile.relative : ℝ) *
                Real.logb 2 (38 / 25)) * b)) := by gcongr
        _ = (Nat.card (A.kernel ≃* A.kernel) : ℝ) *
              (2 : ℝ) ^ (profile.slope * b) := by
          rw [show
            (2 : ℝ) ^ (((profile.binaryPrimary : ℝ) * (1 / 2) +
                (profile.linear : ℝ) * (Real.logb 2 3 / 3) +
                (profile.ordinary : ℝ) * (Real.logb 2 5 / 3)) * b) *
                ((Nat.card (A.kernel ≃* A.kernel) : ℝ) *
                  (2 : ℝ) ^ (((profile.relative : ℝ) *
                    Real.logb 2 (38 / 25)) * b)) =
              (Nat.card (A.kernel ≃* A.kernel) : ℝ) *
                ((2 : ℝ) ^ (((profile.binaryPrimary : ℝ) * (1 / 2) +
                  (profile.linear : ℝ) * (Real.logb 2 3 / 3) +
                  (profile.ordinary : ℝ) * (Real.logb 2 5 / 3)) * b) *
                  (2 : ℝ) ^ (((profile.relative : ℝ) *
                    Real.logb 2 (38 / 25)) * b)) by ring]
          rw [← Real.rpow_add (by norm_num)]
          unfold DegreeTwoPairRelativeProfile.slope
          congr 2
          ring
    have hcast : (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
        (Nat.card Label : ℝ) * (Nat.card (Q ≃* Q) : ℝ) := by
      exact_mod_cast hraw
    calc
      (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
          (Nat.card Label : ℝ) * (Nat.card (Q ≃* Q) : ℝ) := hcast
      _ ≤ ((Nat.card (A.kernel ≃* A.kernel) : ℝ) *
            (2 : ℝ) ^ (profile.slope * b)) *
            (Nat.card (Q ≃* Q) : ℝ) :=
        mul_le_mul_of_nonneg_right hlabel (Nat.cast_nonneg _)
      _ = ((Nat.card (Q ≃* Q) : ℝ) *
            (Nat.card (A.kernel ≃* A.kernel) : ℝ)) *
            (2 : ℝ) ^ (profile.slope * b) := by ring

end DegreeTwoPairBinaryKernelAnchor

namespace DegreeTwoPairRelativeLiftData

/-- Universal pair-relative lift from one binary-kernel anchor on each
literal original quotient. -/
noncomputable def ofBinaryKernelAnchors
    {s : ℕ} {p : PreE7PairActionClass s}
    (lit : PreE7CharacterLiterature)
    (profile :
      {N : Subgroup (preE7PairAction s p) // N.Normal} →
        DegreeTwoPairRelativeProfile)
    (capacity : ∀ N,
      (profile N).slope ≤ preE7CharacterWindow (2 * s))
    (data : ∀ N, DegreeTwoPairBinaryKernelAnchor
      (preE7PairAction s p ⧸ N.1) (profile N)) :
    DegreeTwoPairRelativeLiftData s p where
  profile := profile
  capacity := capacity
  envelope N := (data N).toQuotientEnvelope lit

end DegreeTwoPairRelativeLiftData

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
