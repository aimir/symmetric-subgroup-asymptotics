import SymmetricSubgroupAsymptotics.NormalRestrictionConstituent
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoBinaryKernelAnchor
import SymmetricSubgroupAsymptotics.SylowEpimorphismRestriction

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

private noncomputable def anchorSylow
    {J : Type} [Group J] [Finite J]
    [Invertible (Nat.card J : ℂ)]
    (a : A.AnchorLabel (J := J)) : Sylow 2 (A.anchorSource a) :=
  Classical.choice inferInstance

private def sylowRestrictionOf
    {J : Type} [Group J] [Finite J]
    [Invertible (Nat.card J : ℂ)]
    (a : A.AnchorLabel (J := J))
    (f : GroupEpimorphism (A.anchorSource a) A.kernel) :
    GroupEpimorphism
      (A.anchorSylow a : Subgroup (A.anchorSource a)) A.kernel :=
  sylowEpimorphismRestriction (A.anchorSylow a) A.kernel_twoGroup f

private noncomputable def sylowRestriction
    {J : Type} [Group J] [Finite J]
    [Invertible (Nat.card J : ℂ)]
    (f : GroupEpimorphism J Q) :
    GroupEpimorphism
      (A.anchorSylow (A.anchorLabel f) :
        Subgroup (A.anchorSource (A.anchorLabel f))) A.kernel :=
  A.sylowRestrictionOf (A.anchorLabel f) (A.anchorRestriction f)

private def RelativeLabels
    {J : Type} [Group J] [Finite J]
    [Invertible (Nat.card J : ℂ)]
    (a : A.AnchorLabel (J := J)) : Type :=
  ∀ i, epimorphismCharacterLabels
    (J := (A.anchorSylow a : Subgroup (A.anchorSource a)))
    (A.constituent i).action

/-- A relative character tuple together with the proposition that it comes
from one full epimorphism of the anchor source.  The witness is proof data,
so this subtype has no greater cardinality than `RelativeLabels`. -/
private def CertifiedRelativeLabels
    {J : Type} [Group J] [Finite J]
    [Invertible (Nat.card J : ℂ)]
    (a : A.AnchorLabel (J := J)) : Type :=
  {L : A.RelativeLabels a //
    ∃ f : GroupEpimorphism (A.anchorSource a) A.kernel,
      ∀ i, (L i).1 = Representation.character
        ((A.constituent i).action.comp (A.sylowRestrictionOf a f).1)}

private def Label (J : Type) [Group J] [Finite J]
    [Invertible (Nat.card J : ℂ)] : Type :=
  Σ a : A.AnchorLabel (J := J), A.CertifiedRelativeLabels a

private noncomputable def label
    {J : Type} [Group J] [Finite J]
    [Invertible (Nat.card J : ℂ)]
    (f : GroupEpimorphism J Q) : A.Label J :=
  ⟨A.anchorLabel f,
    ⟨fun i ↦
      ⟨Representation.character
        ((A.constituent i).action.comp (A.sylowRestriction f).1),
        A.sylowRestriction f, rfl⟩,
      A.anchorRestriction f, fun _ ↦ rfl⟩⟩

private noncomputable def relativeRepresentative
    {J : Type} [Group J] [Finite J]
    [Invertible (Nat.card J : ℂ)]
    (d : A.Label J) :
    GroupEpimorphism (A.anchorSource d.1) A.kernel :=
  Classical.choose d.2.2

private theorem relativeRepresentative_spec
    {J : Type} [Group J] [Finite J]
    [Invertible (Nat.card J : ℂ)]
    (d : A.Label J) (i : Fin profile.relative) :
    (d.2.1 i).1 = Representation.character
      ((A.constituent i).action.comp
        (A.sylowRestrictionOf d.1 (A.relativeRepresentative d)).1) :=
  Classical.choose_spec d.2.2 i

private noncomputable def labelKernel
    {J : Type} [Group J] [Finite J]
    [Invertible (Nat.card J : ℂ)]
    (d : A.Label J) (i : Fin profile.relative) : Subgroup J :=
  ((A.constituent i).action.comp (A.relativeRepresentative d).1).ker.map
    (A.anchorSource d.1).subtype

private theorem constituent_units_range_isPGroup (i : Fin profile.relative) :
    IsPGroup 2 (A.constituent i).action.toHomUnits.range :=
  A.kernel_twoGroup.of_surjective
    (A.constituent i).action.toHomUnits.rangeRestrict
    (A.constituent i).action.toHomUnits.rangeRestrict_surjective

private theorem constituent_comp_units_range_isPGroup
    {M : Type} [Group M]
    (i : Fin profile.relative) (f : GroupEpimorphism M A.kernel) :
    IsPGroup 2 ((A.constituent i).action.comp f.1).toHomUnits.range := by
  have hrange : ((A.constituent i).action.comp f.1).toHomUnits.range =
      (A.constituent i).action.toHomUnits.range := by
    apply le_antisymm
    · rintro z ⟨m, rfl⟩
      exact ⟨f.1 m, by apply Units.ext; rfl⟩
    · rintro z ⟨k, rfl⟩
      obtain ⟨m, rfl⟩ := f.2 k
      exact ⟨m, by apply Units.ext; rfl⟩
  rw [hrange]
  exact A.constituent_units_range_isPGroup i

private theorem labelKernel_label
    {J : Type} [Group J] [Finite J]
    [Invertible (Nat.card J : ℂ)]
    (f : GroupEpimorphism J Q) (i : Fin profile.relative) :
    A.labelKernel (A.label f) i =
      ((A.constituent i).action.comp (A.anchorRestriction f).1).ker.map
        (A.anchorSource (A.anchorLabel f)).subtype := by
    let F : GroupEpimorphism
        (A.anchorSource (A.anchorLabel f)) A.kernel :=
      A.relativeRepresentative (A.label f)
    let G := A.anchorRestriction f
    let P := A.anchorSylow (A.anchorLabel f)
    letI : Fintype (P : Subgroup
        (A.anchorSource (A.anchorLabel f))) := Fintype.ofFinite _
    letI : Invertible (Nat.card (P : Subgroup
        (A.anchorSource (A.anchorLabel f))) : ℂ) :=
      invertibleOfNonzero (by
        exact_mod_cast (Nat.card_pos
          (α := (P : Subgroup
            (A.anchorSource (A.anchorLabel f))))).ne')
    have hchar : Representation.character
        ((A.constituent i).action.comp
          (A.sylowRestrictionOf (A.anchorLabel f) F).1) =
      Representation.character
        ((A.constituent i).action.comp (A.sylowRestriction f).1) := by
      have hs := A.relativeRepresentative_spec (A.label f) i
      change Representation.character
          ((A.constituent i).action.comp (A.sylowRestriction f).1) =
        Representation.character
          ((A.constituent i).action.comp
            (A.sylowRestrictionOf (A.anchorLabel f) F).1) at hs
      exact hs.symm
    letI : Representation.IsIrreducible
        ((A.constituent i).action.comp
          (A.sylowRestrictionOf (A.anchorLabel f) F).1) :=
      representation_irreducible_comp (A.constituent i).action
        (A.sylowRestrictionOf (A.anchorLabel f) F).1
        (A.sylowRestrictionOf (A.anchorLabel f) F).2
    letI : Representation.IsIrreducible
        ((A.constituent i).action.comp (A.sylowRestriction f).1) :=
      representation_irreducible_comp (A.constituent i).action
        (A.sylowRestriction f).1 (A.sylowRestriction f).2
    obtain ⟨e⟩ := irreducible_equiv_of_character_eq
      ((A.constituent i).action.comp
        (A.sylowRestrictionOf (A.anchorLabel f) F).1)
      ((A.constituent i).action.comp (A.sylowRestriction f).1) hchar
    have hPker :
        ((A.constituent i).action.comp
          (A.sylowRestrictionOf (A.anchorLabel f) F).1).ker =
          ((A.constituent i).action.comp (A.sylowRestriction f).1).ker :=
      representation_kernel_eq_of_equiv e
    let ff := (A.constituent i).action.comp F.1
    let gg := (A.constituent i).action.comp G.1
    have hPkerUnits :
        (ff.toHomUnits.comp (P : Subgroup
          (A.anchorSource (A.anchorLabel f))).subtype).ker =
          (gg.toHomUnits.comp (P : Subgroup
            (A.anchorSource (A.anchorLabel f))).subtype).ker := by
      ext x
      have hx := SetLike.ext_iff.mp hPker x
      simpa only [ff, gg, sylowRestriction, sylowRestrictionOf,
        sylowEpimorphismRestriction, MonoidHom.mem_ker,
        MonoidHom.comp_apply, Units.ext_iff, MonoidHom.coe_toHomUnits,
        Units.val_one] using hx
    have hu := hom_ker_eq_of_sylow_ker_eq P ff.toHomUnits gg.toHomUnits
      (A.constituent_comp_units_range_isPGroup i F)
      (A.constituent_comp_units_range_isPGroup i G)
      hPkerUnits
    have hfull : ff.ker = gg.ker := by
      simpa only [MonoidHom.ker_toHomUnits] using hu
    change ff.ker.map (A.anchorSource (A.anchorLabel f)).subtype =
      gg.ker.map (A.anchorSource (A.anchorLabel f)).subtype
    exact congrArg
      (fun K : Subgroup (A.anchorSource (A.anchorLabel f)) ↦
        K.map (A.anchorSource (A.anchorLabel f)).subtype) hfull

/-- Equal labels determine the original epimorphism kernel.  The certified
relative label chooses one full anchor-source representative; its mapped
kernel is an ordinary subgroup of the original source and is therefore
stable under equality of dependent sigma labels. -/
private theorem kernel_le_of_label_eq
    {J : Type} [Group J] [Finite J]
    [Invertible (Nat.card J : ℂ)]
    (f g : GroupEpimorphism J Q)
    (h : A.label f = A.label g) : f.1.ker ≤ g.1.ker := by
  have hsource : A.anchorSource (A.anchorLabel f) =
      A.anchorSource (A.anchorLabel g) := by
    have hs := congrArg (fun d : A.Label J ↦ A.anchorSource d.1) h
    exact hs
  have hrelativeKernel (i : Fin profile.relative) :
      ((A.constituent i).action.comp (A.anchorRestriction f).1).ker.map
          (A.anchorSource (A.anchorLabel f)).subtype =
        ((A.constituent i).action.comp (A.anchorRestriction g).1).ker.map
          (A.anchorSource (A.anchorLabel g)).subtype := by
    calc
      _ = A.labelKernel (A.label f) i := (A.labelKernel_label f i).symm
      _ = A.labelKernel (A.label g) i :=
        congrArg (fun d : A.Label J ↦ A.labelKernel d i) h
      _ = _ := A.labelKernel_label g i
  intro x hx
  have hxM : x ∈ A.anchorSource (A.anchorLabel g) := by
    have hxf : x ∈ A.anchorSource (A.anchorLabel f) := by
      rw [A.anchorSource_anchorLabel f]
      change f.1 x ∈ A.kernel
      rw [MonoidHom.mem_ker.mp hx]
      exact A.kernel.one_mem
    rw [← hsource]
    exact hxf
  have hkKernel : g.1 x ∈ A.kernel := by
    change x ∈ A.kernel.comap g.1
    rw [← A.anchorSource_anchorLabel g]
    exact hxM
  have hk := hkKernel
  rw [A.kernel_eq] at hk
  simp only [Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker] at hk
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
      let u : A.kernel := ⟨f.1 (y * x * y⁻¹), by
        exact ((A.anchorRestriction f).1 z).2⟩
      change (A.constituent i).action u = 1
      have hu : u = 1 := by
        apply Subtype.ext
        change f.1 (y * x * y⁻¹) = 1
        rw [map_mul, map_mul, map_inv, MonoidHom.mem_ker.mp hx]
        simp
      rw [hu, map_one]
    have hzmap : (y * x * y⁻¹ : J) ∈
        ((A.constituent i).action.comp (A.anchorRestriction f).1).ker.map
          (A.anchorSource (A.anchorLabel f)).subtype :=
      ⟨z, hzf, rfl⟩
    rw [hrelativeKernel i] at hzmap
    obtain ⟨zg, hzg, hzgval⟩ := hzmap
    have hzg' := MonoidHom.mem_ker.mp hzg
    let lhs : A.kernel := ⟨g.1 zg.1, by
      exact ((A.anchorRestriction g).1 zg).2⟩
    let rhs : A.kernel := ⟨q * (gx : Q) * q⁻¹, by
      exact A.kernel_normal.conj_mem (g.1 x) hkKernel q⟩
    change (A.constituent i).action lhs = 1 at hzg'
    change (zg.1 : J) = y * x * y⁻¹ at hzgval
    have hlr : lhs = rhs := by
      apply Subtype.ext
      change g.1 zg.1 = q * g.1 x * q⁻¹
      rw [hzgval, map_mul, map_mul, map_inv, hy]
    rw [hlr] at hzg'
    exact hzg'

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
  have hc' : (Nat.card (ConjClasses (P : Subgroup J)) : ℝ) ≤
      Nat.card (ConjClasses T) := by exact_mod_cast hc
  exact hc'.trans (hMaroti b T hT.isNilpotent)

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
    letI : Finite (A.PrefixLabel J) := by
      unfold PrefixLabel
      infer_instance
    letI : Finite (A.AnchorLabel (J := J)) :=
      Finite.of_surjective (A.anchorLabel (J := J)) (by
        rintro ⟨a, f, hf⟩
        exact ⟨f, Subtype.ext hf⟩)
    letI (a : A.AnchorLabel (J := J)) : Invertible
        (Nat.card (A.anchorSylow a : Subgroup (A.anchorSource a)) : ℂ) :=
      invertibleOfNonzero (by
        exact_mod_cast (Nat.card_pos
          (α := (A.anchorSylow a : Subgroup (A.anchorSource a)))).ne')
    letI (a : A.AnchorLabel (J := J)) : Finite (A.RelativeLabels a) := by
      unfold RelativeLabels
      infer_instance
    letI (a : A.AnchorLabel (J := J)) :
        Finite (A.CertifiedRelativeLabels a) := by
      unfold CertifiedRelativeLabels
      infer_instance
    letI : Finite (A.Label J) := by
      unfold Label
      infer_instance
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
          _ = (38 / 25 : ℝ) ^ (b : ℝ) :=
            (Real.rpow_natCast _ _).symm
          _ = ((2 : ℝ) ^ Real.logb 2 (38 / 25)) ^ (b : ℝ) := by
            congr 1
            rw [Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)]
          _ = (2 : ℝ) ^ (Real.logb 2 (38 / 25) * b) := by
            rw [Real.rpow_mul (by norm_num)]
      have hcertified (a : A.AnchorLabel (J := J)) :
          (Nat.card (A.CertifiedRelativeLabels a) : ℝ) ≤
            (2 : ℝ) ^ (((profile.relative : ℝ) *
              Real.logb 2 (38 / 25)) * b) := by
        have hcard : Nat.card (A.CertifiedRelativeLabels a) ≤
            Nat.card (A.RelativeLabels a) :=
          Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
        have hcast : (Nat.card (A.CertifiedRelativeLabels a) : ℝ) ≤
            Nat.card (A.RelativeLabels a) := by exact_mod_cast hcard
        exact hcast.trans (hrelative a)
      rw [Label, Nat.card_sigma, Nat.cast_sum]
      calc
        ∑ a : A.AnchorLabel (J := J),
              (Nat.card (A.CertifiedRelativeLabels a) : ℝ) ≤
            ∑ _a : A.AnchorLabel (J := J),
              (2 : ℝ) ^ (((profile.relative : ℝ) *
                Real.logb 2 (38 / 25)) * b) :=
          Finset.sum_le_sum (fun a _ ↦ hcertified a)
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
