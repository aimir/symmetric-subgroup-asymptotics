import SymmetricSubgroupAsymptotics.CFSGReeGTwoFixedFactorDescent
import SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveCoordinates

/-! Exact positive/opposite intersection and positive normalizer inside
the SAME original Ree fixed group. The normalizer equality is derived
from the proved two-cell cover and an explicit nonidentity positive word;
no Sylow or group-order assertion is an input. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoFixedRankOneGeometry
open CFSGReeGTwoFieldParameters CFSGReeGTwoFixedModelEquivalence
open CFSGReeGTwoOriginalPositiveSubgroup CFSGReeGTwoOriginalBorel
open CFSGReeGTwoOriginalOpposition CFSGReeGTwoFixedFactorDescent
open CFSGGTwoOriginalBorel CFSGGTwoOpposedFlagIntersection

theorem positive_le_fixed_borel (m : ℕ) : fixedPositiveGroup m≤borelGroup m := by
  intro u hu
  apply (fixed_borel_iff m u).mp
  exact positive_le_borel (Field m) hu

theorem fixed_positive_nonidentity (m : ℕ) :
    ∃u∈fixedPositiveGroup m,u≠1 := by
  let u := fixedPositiveChart m (![1,0,0]:Fin 3→Field m)
  refine ⟨u.val,u.property,?_⟩
  intro he
  have hu : u=1 := Subtype.ext he
  have hc : fixedPositiveChart m (![1,0,0]:Fin 3→Field m)=fixedPositiveChart m 0 :=
    hu.trans (CFSGReeGTwoPositiveCoordinates.chart_zero m).symm
  have hy := fixedPositiveChart_injective m hc
  have h0 := congrFun hy 0
  change (1:Field m)=0 at h0
  exact one_ne_zero h0

theorem fixed_opposed_positive_intersection (m : ℕ) (u : originalModelFixed m)
    (hu : u∈fixedPositiveGroup m)
    (hb : fixedOpposition m*u*(fixedOpposition m)⁻¹∈borelGroup m) : u=1 := by
  have hraw := (fixed_borel_iff m _).mpr hb
  change longestWord (Field m)*u.val*(longestWord (Field m))⁻¹∈borel (Field m) at hraw
  exact Subtype.ext (original_opposed_positive_intersection (Field m) u.val hu hraw)

theorem fixed_borel_inf_opposite (m : ℕ) :
    borelGroup m ⊓ (fixedPositiveGroup m).map
      (MulAut.conj (fixedOpposition m)).toMonoidHom=⊥ := by
  apply bot_unique
  intro g hg
  obtain ⟨u,hu,he⟩ := hg.2
  have hb : fixedOpposition m*u*(fixedOpposition m)⁻¹∈borelGroup m := by
    change (MulAut.conj (fixedOpposition m)).toMonoidHom u∈borelGroup m
    rw [he]
    exact hg.1
  have hu1 := fixed_opposed_positive_intersection m u hu hb
  apply Subgroup.mem_bot.mpr
  exact he.symm.trans (by rw [hu1,map_one])

theorem fixedOpposition_not_mem_borel (m : ℕ) : fixedOpposition m∉borelGroup m := by
  intro hw
  obtain ⟨u,hu,hn⟩ := fixed_positive_nonidentity m
  apply hn
  apply fixed_opposed_positive_intersection m u hu
  exact (borelGroup m).mul_mem
    ((borelGroup m).mul_mem hw (positive_le_fixed_borel m hu)) ((borelGroup m).inv_mem hw)

theorem fixed_positive_normalizer_eq_borel (m : ℕ) :
    Subgroup.normalizer (fixedPositiveGroup m:Set (originalModelFixed m))=borelGroup m := by
  apply le_antisymm _ (borelGroup_le_normalizer m)
  intro g hg
  rcases fixed_bruhat m g with hb|⟨b,hb,u,hu,he⟩
  · exact hb
  · exfalso
    let N := Subgroup.normalizer (fixedPositiveGroup m:Set (originalModelFixed m))
    have hw : fixedOpposition m∈N := by
      have hmem := N.mul_mem (N.mul_mem
        (N.inv_mem (borelGroup_le_normalizer m hb)) hg)
        (N.inv_mem ((fixedPositiveGroup m).le_normalizer hu))
      have hid : b⁻¹*g*u⁻¹=fixedOpposition m := by rw [he];group
      rwa [hid] at hmem
    obtain ⟨v,hv,hn⟩ := fixed_positive_nonidentity m
    apply hn
    apply fixed_opposed_positive_intersection m v hv
    exact positive_le_fixed_borel m ((Subgroup.mem_normalizer_iff.mp hw v).mp hv)

theorem fixed_positive_normalizer_soluble (m : ℕ) :
    IsSolvable (Subgroup.normalizer (fixedPositiveGroup m:Set (originalModelFixed m))) := by
  rw [fixed_positive_normalizer_eq_borel]
  exact borelGroup_soluble m

end SymmetricSubgroupAsymptotics.CFSGReeGTwoFixedRankOneGeometry
