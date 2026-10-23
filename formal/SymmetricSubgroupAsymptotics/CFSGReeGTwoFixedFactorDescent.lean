import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalBigCellUniqueness
import SymmetricSubgroupAsymptotics.CFSGReeGTwoFixedOrdinaryCells
import SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalBorel

/-! Actual fixed-factor descent, not surjectivity of fixed points on a
quotient. Ordinary U*T and B*w0*U factors are unique in the native flag;
applying the SAME original Ree automorphism therefore fixes each factor.
The resulting two-cell cover is inside the original fixed group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoFixedFactorDescent
open CFSG.Models.Chevalley CFSGGTwoOriginalBorel CFSGGTwoPositiveWordSubgroup
open CFSGGTwoOriginalBigCellUniqueness CFSGGTwoOriginalPositiveRootWords
open CFSGGTwoOriginalRankTwoTorus CFSGReeGTwoOriginalOpposition
open CFSGReeGTwoFieldParameters CFSGReeGTwoOriginalAutomorphism
open CFSGReeGTwoFixedModelEquivalence CFSGReeGTwoOrdinaryBorelTwist
open CFSGReeGTwoOriginalTorus CFSGReeGTwoOriginalPositiveSubgroup
open CFSGReeGTwoOriginalBorel CFSGReeGTwoFixedOrdinaryCells
local notation "A" => CartanMatrix.G₂

theorem ree_longestWord (m : ℕ) :
    reeAutomorphism m (longestWord (Field m))=longestWord (Field m) :=
  (fixedOpposition m).property

theorem fixed_borel_factors (m : ℕ) (g : originalModelFixed m)
    (hg : g.val∈borel (Field m)) :
    ∃ u∈positiveWordGroup (Field m),∃ t∈torus (Field m),
      g.val=u*t ∧ reeAutomorphism m u=u ∧ reeAutomorphism m t=t := by
  obtain ⟨u,hu,t,ht,he⟩ := borel_factor (Field m) g.val hg
  have hh : reeAutomorphism m u*reeAutomorphism m t=u*t := by
    calc
      _=reeAutomorphism m (u*t) := (map_mul _ _ _).symm
      _=g.val := by rw [←he]; exact g.property
      _=u*t := he
  have h := positive_torus_factors_unique (Field m) _ u _ t
    (ree_positive_mem m u hu) hu (ree_torus_mem m t ht) ht hh
  exact ⟨u,hu,t,ht,he,h.1,h.2⟩

theorem fixed_borel_iff (m : ℕ) (g : originalModelFixed m) :
    g.val∈borel (Field m) ↔ g∈borelGroup m := by
  constructor
  · intro hg
    obtain ⟨u,hu,t,ht,he,hfu,hft⟩ := fixed_borel_factors m g hg
    let uf : originalModelFixed m := ⟨u,hfu⟩
    let tf : originalModelFixed m := ⟨t,hft⟩
    have huf : uf∈fixedPositiveGroup m := hu
    have htf : tf∈(fixedTorusHom m).range := (fixed_torus_range_iff m tf).mp ht
    obtain ⟨a,ha⟩ := htf
    refine ⟨⟨⟨uf,huf⟩,a⟩,?_⟩
    apply Subtype.ext
    change u*(fixedTorusHom m a).val=g.val
    rw [ha]
    exact he.symm
  · rintro ⟨x,rfl⟩
    rw [borelHom_apply]
    change x.left.val.val*(fixedTorusHom m x.right).val∈borel (Field m)
    apply (borel (Field m)).mul_mem (positive_le_borel (Field m) x.left.property)
    apply torus_le_borel (Field m)
    exact (fixed_torus_range_iff m (fixedTorusHom m x.right)).mpr ⟨x.right,rfl⟩

private theorem longest_normalizes_torus (m : ℕ) :
    longestWord (Field m)∈Subgroup.normalizer (torus (Field m)) :=
  (Subgroup.normalizer _).pow_mem ((Subgroup.normalizer _).mul_mem
    (short_torus_normalizer (Field m)) (long_torus_normalizer (Field m))) 3

private theorem rotate_right_torus {G : Type*} [Group G] (b w u t : G) :
    b*w*(u*t)=(b*(w*t*w⁻¹))*w*(t⁻¹*u*t) := by group

private theorem ordinary_big_cell_right_positive (m : ℕ)
    (b c : Model A (Field m)) (hb : b∈borel (Field m)) (hc : c∈borel (Field m)) :
    ∃ d∈borel (Field m),∃ u∈positiveWordGroup (Field m),
      b*longestWord (Field m)*c=d*longestWord (Field m)*u := by
  obtain ⟨u,hu,t,ht,he⟩ := borel_factor (Field m) c hc
  have hwt : longestWord (Field m)*t*(longestWord (Field m))⁻¹∈torus (Field m) :=
    ((Subgroup.mem_normalizer_iff.mp (longest_normalizes_torus m)) t).mp ht
  have htu : t⁻¹*u*t∈positiveWordGroup (Field m) := by
    have h := ((Subgroup.mem_normalizer_iff.mp
      (torus_le_positive_normalizer (Field m) ((torus (Field m)).inv_mem ht))) u).mp hu
    simpa only [inv_inv] using h
  refine ⟨b*(longestWord (Field m)*t*(longestWord (Field m))⁻¹),
    (borel (Field m)).mul_mem hb (torus_le_borel (Field m) hwt),t⁻¹*u*t,htu,?_⟩
  rw [he]
  exact rotate_right_torus _ _ _ _

theorem fixed_big_cell_factors (m : ℕ) (g : originalModelFixed m)
    (b u : Model A (Field m)) (hb : b∈borel (Field m))
    (hu : u∈positiveWordGroup (Field m))
    (he : g.val=b*longestWord (Field m)*u) :
    reeAutomorphism m b=b ∧ reeAutomorphism m u=u := by
  have hh : reeAutomorphism m b*longestWord (Field m)*reeAutomorphism m u=
      b*longestWord (Field m)*u := by
    calc
      _=reeAutomorphism m (b*longestWord (Field m)*u) := by
        rw [map_mul,map_mul,ree_longestWord]
      _=g.val := by rw [←he]; exact g.property
      _=_ := he
  exact borel_opposition_positive_factors_unique (Field m) _ b _ u
    (ree_borel_mem m b hb) hb (ree_positive_mem m u hu) hu hh

theorem fixed_bruhat (m : ℕ) (g : originalModelFixed m) :
    g∈borelGroup m ∨ ∃ b∈borelGroup m,∃ u∈fixedPositiveGroup m,
      g=b*fixedOpposition m*u := by
  rcases fixed_ordinary_two_cells m g with hg | ⟨b,hb,c,hc,he⟩
  · exact Or.inl ((fixed_borel_iff m g).mp hg)
  · obtain ⟨d,hd,u,hu,hdu⟩ := ordinary_big_cell_right_positive m b c hb hc
    have hgu := he.trans hdu
    have hf := fixed_big_cell_factors m g d u hd hu hgu
    let df : originalModelFixed m := ⟨d,hf.1⟩
    let uf : originalModelFixed m := ⟨u,hf.2⟩
    refine Or.inr ⟨df,(fixed_borel_iff m df).mp hd,uf,hu,?_⟩
    exact Subtype.ext hgu

end SymmetricSubgroupAsymptotics.CFSGReeGTwoFixedFactorDescent
