import SymmetricSubgroupAsymptotics.NormalRestrictionConstituent
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoBinaryKernelAnchor

/-!
# Relative kernel anchors for the degree-two pair rows

This is the semantic form of the paper's several-anchor count.  A fixed
prefix has normal binary joint kernel `K`.  Each relative irreducible of the
whole target is represented on `K` by one chosen irreducible constituent.
For a source epimorphism, the prefix fixes the single preimage of `K`; the
constituent is then counted on one Sylow subgroup of that preimage.

Equal constituent characters give equal kernels on the Sylow subgroup.
`hom_ker_eq_of_sylow_ker_eq` promotes this to the complete preimage, and
`NormalRestrictionConstituent.action_eq_one_iff_conjugates_mem_constituent_kernel`
recovers the kernel of the original target irreducible.  Thus each relative
slot costs one nilpotent conjugacy-class factor, independently of the number
of constituents in the restriction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- A fixed prefix and relative tail on one target quotient.  The prefix
joint kernel is binary; the complete prefix-plus-tail tuple is faithful. -/
structure DegreeTwoPairRelativeKernelAnchor
    (Q : Type) [Group Q] [Finite Q]
    (profile : DegreeTwoPairRelativeProfile) : Type 1 where
  binary : Fin profile.binaryPrimary → Q →* ℂˣ
  binary_twoGroup : ∀ i, IsPGroup 2 (binary i).range
  linear : Fin profile.linear → Q →* ℂˣ
  ordinary : Fin profile.ordinary → FiniteIrreducibleRepresentation ℂ Q
  relative : Fin profile.relative → FiniteIrreducibleRepresentation ℂ Q
  kernel : Subgroup Q
  [kernel_normal : kernel.Normal]
  kernel_eq : kernel =
    ((⨅ i, (binary i).ker) ⊓ (⨅ i, (linear i).ker)) ⊓
      (⨅ i, (ordinary i).action.ker)
  kernel_twoGroup : IsPGroup 2 kernel
  constituent : ∀ i,
    NormalRestrictionConstituent (relative i).action kernel
  faithful : ∀ q : Q,
    (∀ i, binary i q = 1) →
    (∀ i, linear i q = 1) →
    (∀ i, (ordinary i).action q = 1) →
    (∀ i, (relative i).action q = 1) → q = 1

attribute [instance] DegreeTwoPairRelativeKernelAnchor.kernel_normal

namespace DegreeTwoPairRelativeKernelAnchor

variable {Q : Type} [Group Q] [Finite Q]
  {profile : DegreeTwoPairRelativeProfile}
  (A : DegreeTwoPairRelativeKernelAnchor Q profile)

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

/-- Equal prefix labels select exactly the same source preimage of the
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
      exact hi ▸ hord i
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
      exact hi.symm ▸ hord i

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
    rw [A.anchorSource_anchorLabel f]
    exact hq
  exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩

private noncomputable def anchorSylow
    {J : Type} [Group J] [Finite J]
    [Invertible (Nat.card J : ℂ)]
    (a : A.AnchorLabel (J := J)) : Sylow 2 (A.anchorSource a) :=
  Classical.choice inferInstance

private noncomputable def sylowRestriction
    {J : Type} [Group J] [Finite J]
    [Invertible (Nat.card J : ℂ)]
    (f : GroupEpimorphism J Q) :
    GroupEpimorphism
      (A.anchorSylow (A.anchorLabel f) :
        Subgroup (A.anchorSource (A.anchorLabel f))) A.kernel :=
  sylowEpimorphismRestriction
    (A.anchorSylow (A.anchorLabel f)) A.kernel_twoGroup
    (A.anchorRestriction f)

private def RelativeLabels
    {J : Type} [Group J] [Finite J]
    [Invertible (Nat.card J : ℂ)]
    (a : A.AnchorLabel (J := J)) : Type :=
  ∀ i, epimorphismCharacterLabels
    (J := (A.anchorSylow a : Subgroup (A.anchorSource a)))
    (A.constituent i).action

private def Label (J : Type) [Group J] [Finite J]
    [Invertible (Nat.card J : ℂ)] : Type :=
  Σ a : A.AnchorLabel (J := J), A.RelativeLabels a

private noncomputable def label
    {J : Type} [Group J] [Finite J]
    [Invertible (Nat.card J : ℂ)]
    (f : GroupEpimorphism J Q) : A.Label J :=
  ⟨A.anchorLabel f, fun i ↦
    ⟨Representation.character
      ((A.constituent i).action.comp (A.sylowRestriction f).1),
      A.sylowRestriction f, rfl⟩⟩

private theorem constituent_range_isPGroup (i : Fin profile.relative) :
    IsPGroup 2 (A.constituent i).action.range :=
  A.kernel_twoGroup.of_surjective
    (A.constituent i).action.rangeRestrict
    (A.constituent i).action.rangeRestrict_surjective

private theorem constituent_comp_range_isPGroup
    {M : Type} [Group M]
    (i : Fin profile.relative) (f : GroupEpimorphism M A.kernel) :
    IsPGroup 2 ((A.constituent i).action.comp f.1).range := by
  have hrange : ((A.constituent i).action.comp f.1).range =
      (A.constituent i).action.range := by
    apply le_antisymm
    · rintro z ⟨m, rfl⟩
      exact ⟨f.1 m, rfl⟩
    · rintro z ⟨k, rfl⟩
      obtain ⟨m, rfl⟩ := f.2 k
      exact ⟨m, rfl⟩
  rw [hrange]
  exact A.constituent_range_isPGroup i

/-- Equal labels determine the original epimorphism kernel.  The proof uses
one irreducible constituent per relative slot and promotes its Sylow kernel
to the complete anchor preimage. -/
private theorem kernel_le_of_label_eq
    {J : Type} [Group J] [Finite J]
    [Invertible (Nat.card J : ℂ)]
    (f g : GroupEpimorphism J Q)
    (h : A.label f = A.label g) : f.1.ker ≤ g.1.ker := by
  have ha : A.anchorLabel f = A.anchorLabel g := congrArg Sigma.fst h
  cases ha
  have ht : (fun i ↦
      ⟨Representation.character
        ((A.constituent i).action.comp (A.sylowRestriction f).1),
        A.sylowRestriction f, rfl⟩) =
      (fun i ↦
      ⟨Representation.character
        ((A.constituent i).action.comp (A.sylowRestriction g).1),
        A.sylowRestriction g, rfl⟩) :=
    eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have hrelativeKernel (i : Fin profile.relative) :
      ((A.constituent i).action.comp (A.anchorRestriction f).1).ker =
        ((A.constituent i).action.comp (A.anchorRestriction g).1).ker := by
    let P := A.anchorSylow (A.anchorLabel f)
    have hchar : Representation.character
        ((A.constituent i).action.comp (A.sylowRestriction f).1) =
      Representation.character
        ((A.constituent i).action.comp (A.sylowRestriction g).1) :=
      congrArg Subtype.val (congrFun ht i)
    letI : Representation.IsIrreducible
        ((A.constituent i).action.comp (A.sylowRestriction f).1) :=
      representation_irreducible_comp (A.constituent i).action
        (A.sylowRestriction f).1 (A.sylowRestriction f).2
    letI : Representation.IsIrreducible
        ((A.constituent i).action.comp (A.sylowRestriction g).1) :=
      representation_irreducible_comp (A.constituent i).action
        (A.sylowRestriction g).1 (A.sylowRestriction g).2
    obtain ⟨e⟩ := irreducible_equiv_of_character_eq
      ((A.constituent i).action.comp (A.sylowRestriction f).1)
      ((A.constituent i).action.comp (A.sylowRestriction g).1) hchar
    have hPker :
        ((A.constituent i).action.comp (A.sylowRestriction f).1).ker =
          ((A.constituent i).action.comp (A.sylowRestriction g).1).ker :=
      representation_kernel_eq_of_equiv e
    exact hom_ker_eq_of_sylow_ker_eq P
      ((A.constituent i).action.comp (A.anchorRestriction f).1)
      ((A.constituent i).action.comp (A.anchorRestriction g).1)
      (A.constituent_comp_range_isPGroup i (A.anchorRestriction f))
      (A.constituent_comp_range_isPGroup i (A.anchorRestriction g)) hPker
  intro x hx
  have hxM : x ∈ A.anchorSource (A.anchorLabel g) := by
    have hxf : x ∈ A.anchorSource (A.anchorLabel f) := by
      rw [A.anchorSource_anchorLabel f]
      change f.1 x ∈ A.kernel
      rw [MonoidHom.mem_ker.mp hx]
      exact A.kernel.one_mem
    exact hxf
  have hkKernel : g.1 x ∈ A.kernel := by
    rw [← A.anchorSource_anchorLabel g]
    exact hxM
  have hk := hkKernel
  rw [A.kernel_eq] at hk
  apply MonoidHom.mem_ker.mpr
  apply A.faithful (g.1 x)
  · intro i
    exact hk.1.1 i
  · intro i
    exact hk.1.2 i
  · intro i
    exact hk.2 i
  · intro i
    let gx : A.kernel := ⟨g.1 x, hkKernel⟩
    apply (A.constituent i).action_eq_one_of_conjugates_mem_constituent_kernel gx
    intro q
    obtain ⟨y, hy⟩ := g.2 q
    let z : A.anchorSource (A.anchorLabel f) :=
      ⟨y * x * y⁻¹, by
        rw [A.anchorSource_anchorLabel f]
        change f.1 (y * x * y⁻¹) ∈ A.kernel
        rw [map_mul, map_mul, map_inv, MonoidHom.mem_ker.mp hx]
        simp⟩
    have hzf : z ∈
        ((A.constituent i).action.comp (A.anchorRestriction f).1).ker := by
      apply MonoidHom.mem_ker.mpr
      change (A.constituent i).action ⟨f.1 (y * x * y⁻¹), _⟩ = 1
      rw [map_mul, map_mul, map_inv, MonoidHom.mem_ker.mp hx]
      simp
    rw [hrelativeKernel i] at hzf
    have hzg := MonoidHom.mem_ker.mp hzf
    change (A.constituent i).action ⟨g.1 (y * x * y⁻¹), _⟩ = 1 at hzg
    simpa only [map_mul, map_inv, hy] using hzg
  · exact MonoidHom.mem_ker.mp hx

private theorem kernel_eq_of_label_eq
    {J : Type} [Group J] [Finite J]
    [Invertible (Nat.card J : ℂ)]
    (f g : GroupEpimorphism J Q)
    (h : A.label f = A.label g) : f.1.ker = g.1.ker :=
  le_antisymm (A.kernel_le_of_label_eq f g h)
    (A.kernel_le_of_label_eq g f h.symm)

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

private theorem sylow_conjugacyClass_bound
    (hMaroti : NilpotentConjugacyClassInput)
    {J : Type} [Group J] [Finite J]
    (b : ℕ) (action : J →* Equiv.Perm (Fin b))
    (action_injective : Function.Injective action)
    (P : Sylow 2 J) :
    (Nat.card (ConjClasses (P : Subgroup J)) : ℝ) ≤
      (38 / 25 : ℝ) ^ b := by
  let T := (P : Subgroup J).map action
  let e : (P : Subgroup J) ≃* T :=
    Subgroup.equivMapOfInjective (P : Subgroup J) action action_injective
  have hT : IsPGroup 2 T := P.isPGroup'.of_equiv e
  have hc : Nat.card (ConjClasses (P : Subgroup J)) ≤
      Nat.card (ConjClasses T) :=
    Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
      (ConjClasses.map_surjective e.symm.surjective)
  exact (by exact_mod_cast hc).trans (hMaroti b T hT.isNilpotent)

/-- The complete anchored relative quotient envelope.  Every relative slot
is charged once at `log_2(38/25)`, while the prefix retains the published
binary-linear, linear, and ordinary source costs. -/
noncomputable def toQuotientEnvelope
    (lit : PreE7CharacterLiterature) :
    DegreeTwoPairRelativeQuotientEnvelope Q profile where
  coefficient := Nat.card (Q ≃* Q)
  coefficient_nonneg := Nat.cast_nonneg _
  bound := by
    intro b J
    letI : Invertible (Nat.card J : ℂ) :=
      invertibleOfNonzero (by exact_mod_cast (Nat.card_pos (α := J)).ne')
    have hlabel : (Nat.card (A.Label J) : ℝ) ≤
        (2 : ℝ) ^ (profile.slope * b) := by
      letI : Fintype (A.AnchorLabel (J := J)) := Fintype.ofFinite _
      have hbin : ((∏ i, Nat.card
          (linearCharacterLabels (J := J) (A.binary i)) : ℕ) : ℝ) ≤
          (2 : ℝ) ^ (((profile.binaryPrimary : ℝ) * (1 / 2)) * b) := by
        apply product_card_le_two_rpow
        intro i
        have h := binaryLinearCharacterSet_card_le
          lit.kovacsPraegerBinary b J
          (linearCharacterLabels (J := J) (A.binary i))
          (linearCharacterLabels_twoGroup _ (A.binary_twoGroup i))
        convert h using 1 <;> ring
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
        simp only [PrefixLabel, Nat.card_prod, Nat.card_pi]
        push_cast
        calc
          (Nat.card (∀ i, linearCharacterLabels (J := J) (A.binary i)) : ℝ) *
                (Nat.card (∀ i, linearCharacterLabels (J := J) (A.linear i)) : ℝ) *
                (Nat.card (∀ i, epimorphismCharacterLabels
                  (J := J) (A.ordinary i).action) : ℝ) ≤
              (2 : ℝ) ^ (((profile.binaryPrimary : ℝ) * (1 / 2)) * b) *
                (2 : ℝ) ^ (((profile.linear : ℝ) *
                  (Real.logb 2 3 / 3)) * b) *
                (2 : ℝ) ^ (((profile.ordinary : ℝ) *
                  (Real.logb 2 5 / 3)) * b) := by gcongr
          _ = _ := by rw [three_rpow_mul]; congr 2 <;> ring
      have hrelative (a : A.AnchorLabel (J := J)) :
          (Nat.card (A.RelativeLabels a) : ℝ) ≤
            (2 : ℝ) ^ (((profile.relative : ℝ) *
              Real.logb 2 (38 / 25)) * b) := by
        simp only [RelativeLabels, Nat.card_pi]
        apply product_card_le_two_rpow
        intro i
        have h1 := epimorphismCharacterLabels_card
          (J := (A.anchorSylow a : Subgroup (A.anchorSource a)))
          (A.constituent i).action
        let action : A.anchorSource a →* Equiv.Perm (Fin b) :=
          J.subtype.comp (A.anchorSource a).subtype
        have hinjective : Function.Injective action := by
          intro x y hxy
          exact Subtype.ext (Subtype.ext hxy)
        have h2 := sylow_conjugacyClass_bound lit.maroti b action hinjective
          (A.anchorSylow a)
        calc
          (Nat.card (epimorphismCharacterLabels
              (J := (A.anchorSylow a : Subgroup (A.anchorSource a)))
              (A.constituent i).action) : ℝ) ≤
              Nat.card (ConjClasses
                (A.anchorSylow a : Subgroup (A.anchorSource a))) := by
                  exact_mod_cast h1
          _ ≤ (38 / 25 : ℝ) ^ b := h2
          _ = (2 : ℝ) ^ (Real.logb 2 (38 / 25) * b) := by
            rw [show (38 / 25 : ℝ) ^ b =
              (2 : ℝ) ^ (Real.logb 2 (38 / 25) * (b : ℝ)) by
                rw [Real.rpow_natCast, Real.rpow_mul (by norm_num),
                  Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)]]
      rw [Label, Nat.card_sigma, Nat.cast_sum]
      calc
        ∑ a : A.AnchorLabel (J := J), (Nat.card (A.RelativeLabels a) : ℝ) ≤
            ∑ _a : A.AnchorLabel (J := J),
              (2 : ℝ) ^ (((profile.relative : ℝ) *
                Real.logb 2 (38 / 25)) * b) :=
          Finset.sum_le_sum (fun a _ ↦ hrelative a)
        _ = (Nat.card (A.AnchorLabel (J := J)) : ℝ) *
            (2 : ℝ) ^ (((profile.relative : ℝ) *
              Real.logb 2 (38 / 25)) * b) := by
          simp only [Finset.sum_const, Finset.card_univ,
            Fintype.card_eq_nat_card, nsmul_eq_mul]
        _ ≤ (2 : ℝ) ^ (((profile.binaryPrimary : ℝ) * (1 / 2) +
              (profile.linear : ℝ) * (Real.logb 2 3 / 3) +
              (profile.ordinary : ℝ) * (Real.logb 2 5 / 3)) * b) *
            (2 : ℝ) ^ (((profile.relative : ℝ) *
              Real.logb 2 (38 / 25)) * b) := by gcongr
        _ = (2 : ℝ) ^ (profile.slope * b) := by
          rw [← Real.rpow_add (by norm_num)]
          unfold DegreeTwoPairRelativeProfile.slope
          congr 2
          ring
    have hraw := groupEpimorphism_card_le_kernel_labels
      (A.label (J := J)) (A.kernel_eq_of_label_eq (J := J))
    have hcast : (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
        (Nat.card (A.Label J) : ℝ) * (Nat.card (Q ≃* Q) : ℝ) := by
      exact_mod_cast hraw
    calc
      (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
          (Nat.card (A.Label J) : ℝ) * (Nat.card (Q ≃* Q) : ℝ) :=
        hcast
      _ ≤ (2 : ℝ) ^ (profile.slope * b) *
          (Nat.card (Q ≃* Q) : ℝ) :=
        mul_le_mul_of_nonneg_right hlabel (Nat.cast_nonneg _)
      _ = (Nat.card (Q ≃* Q) : ℝ) *
          (2 : ℝ) ^ (profile.slope * b) := by ring

end DegreeTwoPairRelativeKernelAnchor

namespace DegreeTwoPairRelativeLiftData

/-- Universal all-original-normal lift from the proved relative-kernel
anchor theorem. -/
noncomputable def ofRelativeKernelAnchors
    {s : ℕ} {p : PreE7PairActionClass s}
    (lit : PreE7CharacterLiterature)
    (profile :
      {N : Subgroup (preE7PairAction s p) // N.Normal} →
        DegreeTwoPairRelativeProfile)
    (capacity : ∀ N,
      (profile N).slope ≤ preE7CharacterWindow (2 * s))
    (data : ∀ N, DegreeTwoPairRelativeKernelAnchor
      (preE7PairAction s p ⨸ N.1) (profile N)) :
    DegreeTwoPairRelativeLiftData s p where
  profile := profile
  capacity := capacity
  envelope N := (data N).toQuotientEnvelope lit

end DegreeTwoPairRelativeLiftData

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
