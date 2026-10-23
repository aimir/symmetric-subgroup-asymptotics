import SymmetricSubgroupAsymptotics.CFSGReeGTwoIndexPointUpper
import SymmetricSubgroupAsymptotics.CFSGRankOneSylowAlignment

/-! The actual derived subgroup itself has a rank-one two-cell cover.
Its opposition is an actual torus translate of the original opposition,
obtained inside the derived group, not assumed to belong to it. This
supplies inner Sylow-pair alignment without full-fixed-group perfectness. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoDerivedBruhat
open CFSGReeGTwoFieldParameters CFSGReeGTwoFixedModelEquivalence
open CFSGReeGTwoOriginalPositiveSubgroup CFSGReeGTwoOriginalBorel
open CFSGReeGTwoOriginalTorus CFSGReeGTwoOriginalOpposition
open CFSGReeGTwoFixedFactorDescent CFSGReeGTwoFixedRankOneGeometry
open CFSGReeGTwoFixedCardinalitySylow CFSGReeGTwoPositiveDerived
open CFSGReeGTwoBorelCore CFSGReeGTwoOppositionTorus CFSGReeGTwoIndexPointUpper
attribute [local instance] fixedModel_finite

private theorem remove_positive_factors {G : Type*} [Group G]
    (v t w u d : G) (he : d=(v*t)*w*u) : v⁻¹*d*u⁻¹=t*w := by
  rw [he]
  group

theorem exists_derived_opposition_parameter (m : ℕ) (hm : 1≤m) :
    ∃t : (Field m)ˣ,fixedTorusHom m t*fixedOpposition m∈commutator (originalModelFixed m) := by
  have hex : ∃d : commutator (originalModelFixed m),d.val∉borelGroup m := by
    by_contra hn
    apply derivedPointStabilizer_proper m hm
    apply top_unique
    intro d _
    exact Classical.byContradiction (fun hd => hn ⟨d,hd⟩)
  obtain ⟨d,hd⟩ := hex
  obtain ⟨b,hb,u,hu,he⟩ := (fixed_bruhat m d.val).resolve_left hd
  obtain ⟨x,rfl⟩ := hb
  have hvD := fixedPositiveGroup_le_commutator m hm x.left.property
  have huD := fixedPositiveGroup_le_commutator m hm hu
  refine ⟨x.right,?_⟩
  have hid := remove_positive_factors x.left.val (fixedTorusHom m x.right)
    (fixedOpposition m) u d.val he
  rw [←hid]
  exact (commutator (originalModelFixed m)).mul_mem
    ((commutator (originalModelFixed m)).mul_mem
      ((commutator (originalModelFixed m)).inv_mem hvD) d.property)
    ((commutator (originalModelFixed m)).inv_mem huD)

def derivedOppositionParameter (m : ℕ) (hm : 1≤m) : (Field m)ˣ :=
  Classical.choose (exists_derived_opposition_parameter m hm)

def derivedOpposition (m : ℕ) (hm : 1≤m) : commutator (originalModelFixed m) :=
  ⟨fixedTorusHom m (derivedOppositionParameter m hm)*fixedOpposition m,
    Classical.choose_spec (exists_derived_opposition_parameter m hm)⟩

def derivedPositiveSylow (m : ℕ) (hm : 1≤m) : Sylow 3 (commutator (originalModelFixed m)) :=
  (fixedPositiveSylow m).subtype (fixedPositiveGroup_le_commutator m hm)

theorem derivedOpposition_not_mem_borel (m : ℕ) (hm : 1≤m) :
    derivedOpposition m hm∉derivedPointStabilizer m := by
  intro hw
  have hh := (borelGroup m).mul_mem
    ((borelGroup m).inv_mem (fixedTorus_mem_borel m (derivedOppositionParameter m hm))) hw
  have he : (fixedTorusHom m (derivedOppositionParameter m hm))⁻¹*
      (derivedOpposition m hm).val=fixedOpposition m := by
    change (fixedTorusHom m _)⁻¹*(fixedTorusHom m _*fixedOpposition m)=_
    exact inv_mul_cancel_left _ _
  change (fixedTorusHom m (derivedOppositionParameter m hm))⁻¹*
    (derivedOpposition m hm).val∈borelGroup m at hh
  rw [he] at hh
  exact fixedOpposition_not_mem_borel m hh

theorem derived_borel_normalizer (m : ℕ) (hm : 1≤m) :
    derivedPointStabilizer m=
      Subgroup.normalizer (derivedPositiveSylow m hm:Set (commutator (originalModelFixed m))) := by
  change (borelGroup m).subgroupOf (commutator (originalModelFixed m))=_
  rw [←fixed_positive_normalizer_eq_borel]
  exact Subgroup.subgroupOf_normalizer_eq (fixedPositiveGroup_le_commutator m hm)

private theorem remove_torus_translate {G : Type*} [Group G] (b w u t : G) :
    (b*w*u)*u⁻¹*(t*w)⁻¹=b*t⁻¹ := by group

theorem derived_two_cells (m : ℕ) (hm : 1≤m) (g : commutator (originalModelFixed m)) :
    g∈derivedPointStabilizer m ∨
      ∃(b : derivedPointStabilizer m) (u : derivedPositiveSylow m hm),
        g=b.val*derivedOpposition m hm*u.val := by
  rcases fixed_bruhat m g.val with hb | ⟨b,hb,u,hu,he⟩
  · exact Or.inl hb
  · let ud : commutator (originalModelFixed m) :=
      ⟨u,fixedPositiveGroup_le_commutator m hm hu⟩
    let bd := g*ud⁻¹*(derivedOpposition m hm)⁻¹
    have hbd : bd∈derivedPointStabilizer m := by
      change g.val*u⁻¹*(fixedTorusHom m (derivedOppositionParameter m hm)*fixedOpposition m)⁻¹∈
        borelGroup m
      rw [he,remove_torus_translate]
      exact (borelGroup m).mul_mem hb
        ((borelGroup m).inv_mem (fixedTorus_mem_borel m _))
    refine Or.inr ⟨⟨bd,hbd⟩,⟨ud,hu⟩,?_⟩
    change g=(g*ud⁻¹*(derivedOpposition m hm)⁻¹)*derivedOpposition m hm*ud
    group

theorem exists_inner_fix_derived_opposite_pair (m : ℕ) (hm : 1≤m)
    (f : MulAut (commutator (originalModelFixed m))) :
    ∃g : commutator (originalModelFixed m),
      (MulAut.conj g*f) • derivedPositiveSylow m hm=derivedPositiveSylow m hm ∧
      (MulAut.conj g*f) • (derivedOpposition m hm • derivedPositiveSylow m hm)=
        derivedOpposition m hm • derivedPositiveSylow m hm := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact CFSGRankOneSylowAlignment.exists_inner_fix_pair
    (derivedPositiveSylow m hm) (derivedPointStabilizer m) (derivedOpposition m hm)
    (derived_borel_normalizer m hm) (derivedOpposition_not_mem_borel m hm)
    (derived_two_cells m hm) f

end SymmetricSubgroupAsymptotics.CFSGReeGTwoDerivedBruhat
