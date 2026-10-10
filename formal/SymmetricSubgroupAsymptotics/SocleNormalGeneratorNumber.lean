import SymmetricSubgroupAsymptotics.ZmudFaithfulCharacterInput
import SymmetricSubgroupAsymptotics.MarkedC4GeneratorNumbers

/-!
# Socle normal-generator number

The affine degree arguments naturally produce inequalities for the least
normal-generator number.  Zmud's theorem is consumed through an exactly
`Fin t`-indexed tuple.  This file proves that these are the same datum for a
finite group, including the padding by identity elements.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- A normal-generating tuple can be padded by identities without changing
its normal closure. -/
theorem exists_normal_generating_tuple_of_length_le
    {G : Type} [Group G] {N : Subgroup G} [N.Normal]
    {d t : ℕ} (g : Fin d → G)
    (hgN : ∀ i, g i ∈ N)
    (hg : Subgroup.normalClosure (Set.range g) = N)
    (hdt : d ≤ t) :
    ∃ x : Fin t → G, Subgroup.normalClosure (Set.range x) = N := by
  let e : Fin d → Fin t := Fin.castLE hdt
  have he : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun x : Fin t => x.val) hij
  let x : Fin t → G := Function.extend e g (fun _ => 1)
  refine ⟨x, le_antisymm ?_ ?_⟩
  · apply Subgroup.normalClosure_le_normal
    rintro y ⟨i, rfl⟩
    by_cases hi : ∃ j, e j = i
    · obtain ⟨j, rfl⟩ := hi
      change Function.extend e g (fun _ => 1) (e j) ∈ N
      rw [he.extend_apply]
      exact hgN j
    · change Function.extend e g (fun _ => 1) i ∈ N
      rw [Function.extend_apply' _ _ _ hi]
      exact N.one_mem
  · rw [← hg]
    apply Subgroup.normalClosure_mono
    rintro y ⟨i, rfl⟩
    refine ⟨e i, ?_⟩
    change Function.extend e g (fun _ => 1) (e i) = g i
    exact he.extend_apply g (fun _ => 1) i

/-- A finite normal subgroup whose least normal-generator number is at most
`t` admits the padded tuple used by the character theorem. -/
theorem exists_normal_generating_tuple_of_normalGen_le
    {G : Type} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] {t : ℕ}
    (h : MarkedC4.normalGen N ≤ t) :
    ∃ x : Fin t → G, Subgroup.normalClosure (Set.range x) = N := by
  obtain ⟨s, hsCard, hsN, hsClosure⟩ := MarkedC4.normalGen_spec N
  let e : {x // x ∈ s} ≃ Fin s.card := s.equivFin
  let g : Fin s.card → G := fun i => (e.symm i).1
  have hgN : ∀ i, g i ∈ N := fun i => hsN (e.symm i).2
  have hrange : Set.range g = (s : Set G) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm i).2
    · intro hx
      refine ⟨e ⟨x, hx⟩, ?_⟩
      exact congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)
  have hg : Subgroup.normalClosure (Set.range g) = N := by
    rw [hrange]
    exact hsClosure
  exact exists_normal_generating_tuple_of_length_le g hgN hg
    (by simpa only [hsCard] using h)

/-- The exact `Fin t` socle witness consumed by Zmud is equivalent to the
least-normal-generator inequality used by the structural degree arguments. -/
theorem socleNormalGeneratorBound_iff_normalGen_le
    (G : Type) [Group G] [Finite G] (t : ℕ) :
    SocleNormalGeneratorBound G t ↔
      MarkedC4.normalGen (finiteGroupSocle G) ≤ t := by
  constructor
  · rintro ⟨x, hx⟩
    let s : Finset G := Finset.univ.image x
    have hsSub : (s : Set G) ⊆ finiteGroupSocle G := by
      intro y hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      rw [← hx]
      exact Subgroup.subset_normalClosure (Set.mem_range_self i)
    have hsClosure : Subgroup.normalClosure (s : Set G) =
        finiteGroupSocle G := by
      apply le_antisymm
      · exact Subgroup.normalClosure_le_normal hsSub
      · rw [← hx]
        apply Subgroup.normalClosure_mono
        rintro y ⟨i, rfl⟩
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    calc
      MarkedC4.normalGen (finiteGroupSocle G) ≤ s.card :=
        MarkedC4.normalGen_le hsSub hsClosure
      _ ≤ Finset.univ.card := Finset.card_image_le
      _ = t := Finset.card_fin t
  · intro h
    exact exists_normal_generating_tuple_of_normalGen_le
      (finiteGroupSocle G) h

namespace SocleNormalGeneratorBound

/-- A socle normal-generator certificate may be padded by identity
elements.  This is the direct tuple form used by the finite package
constructors, so callers do not need to pass through the numerical
`normalGen` invariant. -/
theorem mono {G : Type} [Group G] {m n : ℕ}
    (h : SocleNormalGeneratorBound G m) (hmn : m ≤ n) :
    SocleNormalGeneratorBound G n := by
  obtain ⟨x, hx⟩ := h
  exact exists_normal_generating_tuple_of_length_le x
    (fun i ↦ by
      rw [← hx]
      exact Subgroup.subset_normalClosure (Set.mem_range_self i))
    hx hmn

end SocleNormalGeneratorBound

/-- Generator-number form of the published Zmud input. -/
noncomputable def ZmudFaithfulCharacterTupleInput.ofNormalGen
    (hZmud : ZmudFaithfulCharacterTupleInput)
    {G : Type} [Group G] [Finite G] {t : ℕ}
    (h : MarkedC4.normalGen (finiteGroupSocle G) ≤ t) :
    CharacterQuotientCertificate G :=
  hZmud.generalCertificate
    ((socleNormalGeneratorBound_iff_normalGen_le G t).2 h)

end SymmetricSubgroupAsymptotics

end
