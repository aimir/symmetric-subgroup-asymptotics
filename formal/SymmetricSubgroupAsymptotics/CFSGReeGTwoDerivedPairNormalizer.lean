import SymmetricSubgroupAsymptotics.CFSGReeGTwoDerivedBruhat

/-! The actual opposite Sylow pair in the derived group has exactly the
actual derived torus as pair normalizer. Inner pair alignment therefore
also preserves that same torus; no abstract torus lift is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoDerivedPairNormalizer
open CFSGReeGTwoFieldParameters CFSGReeGTwoFixedModelEquivalence
open CFSGReeGTwoOriginalPositiveSubgroup CFSGReeGTwoOriginalBorel
open CFSGReeGTwoOriginalTorus CFSGReeGTwoOriginalOpposition
open CFSGReeGTwoPositiveDerived CFSGReeGTwoFixedRankOneGeometry
open CFSGReeGTwoBorelCore CFSGReeGTwoOppositionTorus
open CFSGReeGTwoDerivedBruhat CFSGReeGTwoIndexPointUpper

def derivedTorus (m : ℕ) : Subgroup (commutator (originalModelFixed m)) :=
  (fixedTorusHom m).range.subgroupOf (commutator (originalModelFixed m))

def derivedOpposite (m : ℕ) (hm : 1≤m) : Subgroup (commutator (originalModelFixed m)) :=
  (derivedPositiveSylow m hm:Subgroup (commutator (originalModelFixed m))).map (MulAut.conj (derivedOpposition m hm)).toMonoidHom

private theorem torus_translate_square {G : Type*} [Group G] (t w : G)
    (hw : w*w=1) (ht : w*t*w⁻¹=t⁻¹) : (t*w)*(t*w)=1 := by
  calc
    _=t*(w*t*w⁻¹)*(w*w) := by group
    _=1 := by rw [ht,hw,mul_inv_cancel,one_mul]

theorem derivedOpposition_square (m : ℕ) (hm : 1≤m) :
    derivedOpposition m hm*derivedOpposition m hm=1 := by
  apply Subtype.ext
  exact torus_translate_square (fixedTorusHom m (derivedOppositionParameter m hm))
    (fixedOpposition m) (fixedOpposition_square m)
    (by simpa only [map_inv] using fixedOpposition_fixedTorus m (derivedOppositionParameter m hm))

private theorem conjugation_twice {G : Type*} [Group G] (w g : G)
    (hw : w*w=1) : w*(w*g*w⁻¹)*w⁻¹=g := by
  have hi : w⁻¹=w := inv_eq_of_mul_eq_one_right hw
  calc
    _=(w*w)*g*(w*w) := by rw [hi]; group
    _=g := by rw [hw,one_mul,mul_one]

private theorem opposed_normalizer_member {G : Type*} [Group G]
    (U : Subgroup G) (w g : G) (hw : w*w=1)
    (hg : g∈Subgroup.normalizer (U.map (MulAut.conj w).toMonoidHom)) :
    w*g*w⁻¹∈Subgroup.normalizer U := by
  rw [←Subgroup.map_equiv_normalizer_eq] at hg
  obtain ⟨x,hx,he⟩ := hg
  change w*x*w⁻¹=g at he
  rw [←he,conjugation_twice w x hw]
  exact hx

private theorem remove_torus_conjugation {G : Type*} [Group G]
    (t w g : G) : t⁻¹*((t*w)*g*(t*w)⁻¹)*t=w*g*w⁻¹ := by group

theorem derived_pair_normalizer_le_torus (m : ℕ) (hm : 1≤m) :
    Subgroup.normalizer (derivedPositiveSylow m hm:Set (commutator (originalModelFixed m))) ⊓
      Subgroup.normalizer (derivedOpposite m hm:Set (commutator (originalModelFixed m)))≤derivedTorus m := by
  intro g hg
  have hgB : g∈derivedPointStabilizer m := (derived_borel_normalizer m hm).symm ▸ hg.1
  have hop := opposed_normalizer_member (derivedPositiveSylow m hm:Subgroup (commutator (originalModelFixed m)))
    (derivedOpposition m hm) g (derivedOpposition_square m hm) hg.2
  have hopB : derivedOpposition m hm*g*(derivedOpposition m hm)⁻¹∈derivedPointStabilizer m :=
    (derived_borel_normalizer m hm).symm ▸ hop
  have htwB : fixedOpposition m*g.val*(fixedOpposition m)⁻¹∈borelGroup m := by
    have hh := (borelGroup m).mul_mem
      ((borelGroup m).mul_mem
        ((borelGroup m).inv_mem (fixedTorus_mem_borel m (derivedOppositionParameter m hm))) hopB)
      (fixedTorus_mem_borel m (derivedOppositionParameter m hm))
    change (fixedTorusHom m (derivedOppositionParameter m hm))⁻¹*
      ((fixedTorusHom m (derivedOppositionParameter m hm)*fixedOpposition m)*g.val*
        (fixedTorusHom m (derivedOppositionParameter m hm)*fixedOpposition m)⁻¹)*
      fixedTorusHom m (derivedOppositionParameter m hm)∈borelGroup m at hh
    rwa [remove_torus_conjugation] at hh
  exact opposed_borel_mem_torus m g.val hgB htwB

private theorem translate_torus_conjugation {G : Type*} [Group G]
    (t a w : G) (hc : Commute t a) (hw : w*a*w⁻¹=a⁻¹) :
    (t*w)*a*(t*w)⁻¹=a⁻¹ := by
  calc
    _=t*(w*a*w⁻¹)*t⁻¹ := by group
    _=t*a⁻¹*t⁻¹ := by rw [hw]
    _=a⁻¹ := by rw [hc.inv_right.eq,mul_assoc,mul_inv_cancel,mul_one]

theorem derivedTorus_le_pair_normalizer (m : ℕ) (hm : 1≤m) :
    derivedTorus m≤Subgroup.normalizer (derivedPositiveSylow m hm:Set (commutator (originalModelFixed m))) ⊓
      Subgroup.normalizer (derivedOpposite m hm:Set (commutator (originalModelFixed m))) := by
  intro g hg
  have hgRaw : g.val∈(fixedTorusHom m).range := hg
  obtain ⟨t,ht⟩ := hgRaw
  have hgU : g∈Subgroup.normalizer (derivedPositiveSylow m hm:Set (commutator (originalModelFixed m))) := by
    rw [←derived_borel_normalizer]
    change g.val∈borelGroup m
    rw [←ht]
    exact fixedTorus_mem_borel m t
  refine ⟨hgU,?_⟩
  change g∈Subgroup.normalizer
    (((derivedPositiveSylow m hm:Subgroup (commutator (originalModelFixed m))).map
      (MulAut.conj (derivedOpposition m hm)).toMonoidHom):Set (commutator (originalModelFixed m)))
  rw [←Subgroup.map_equiv_normalizer_eq]
  have hInvU := (Subgroup.normalizer (derivedPositiveSylow m hm:Set (commutator (originalModelFixed m)))).inv_mem hgU
  refine ⟨g⁻¹,hInvU,?_⟩
  apply Subtype.ext
  change (derivedOpposition m hm).val*g.val⁻¹*((derivedOpposition m hm).val)⁻¹=g.val
  rw [←ht]
  change (fixedTorusHom m (derivedOppositionParameter m hm)*fixedOpposition m)*
    (fixedTorusHom m t)⁻¹*(fixedTorusHom m (derivedOppositionParameter m hm)*fixedOpposition m)⁻¹=_
  have hc : Commute (fixedTorusHom m (derivedOppositionParameter m hm)) (fixedTorusHom m t)⁻¹ := by
    simpa only [map_inv] using (Commute.all (derivedOppositionParameter m hm) t⁻¹).map (fixedTorusHom m)
  have hw : fixedOpposition m*(fixedTorusHom m t)⁻¹*(fixedOpposition m)⁻¹=
      ((fixedTorusHom m t)⁻¹)⁻¹ := by rw [←map_inv,fixedOpposition_fixedTorus,map_inv]
  simpa only [inv_inv] using translate_torus_conjugation
    (fixedTorusHom m (derivedOppositionParameter m hm)) (fixedTorusHom m t)⁻¹ (fixedOpposition m) hc hw

theorem derived_pair_normalizer_eq_torus (m : ℕ) (hm : 1≤m) :
    Subgroup.normalizer (derivedPositiveSylow m hm:Set (commutator (originalModelFixed m))) ⊓
      Subgroup.normalizer (derivedOpposite m hm:Set (commutator (originalModelFixed m)))=derivedTorus m :=
  le_antisymm (derived_pair_normalizer_le_torus m hm) (derivedTorus_le_pair_normalizer m hm)

end SymmetricSubgroupAsymptotics.CFSGReeGTwoDerivedPairNormalizer
