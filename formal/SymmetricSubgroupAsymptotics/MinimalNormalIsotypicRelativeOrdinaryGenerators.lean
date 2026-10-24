import SymmetricSubgroupAsymptotics.MinimalNormalInternalFactorOrdinaryGenerators
import Mathlib.Algebra.Group.Pi.Lemmas

/-! Genuine ordinary relative generation from one supported coordinate
of an ACTUAL minimal normal subgroup. The chart, selected coordinate,
embedding into the original group, and actual quotient marking are
retained. Conjugate closure is proved from minimality; internal normality
supplies the normalizer condition needed for ordinary sharing. No bound
on the genuine rank of the coordinate group is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MinimalNormalIsotypicRelativeOrdinaryGenerators

variable {G T I : Type} [Group G] [Group T] [Fintype I]
    (E : Subgroup G) (e : E ≃* (I → T)) (i : I)

/-- One actual factor of the charted subgroup, before ambient inclusion. -/
def axisMap : T →* E :=
  e.symm.toMonoidHom.comp (MonoidHom.mulSingle (fun _ : I => T) i)

/-- The selected factor's literal original ambient marking. -/
def axisHom : T →* G := E.subtype.comp (axisMap E e i)

def axis : Subgroup E := (axisMap E e i).range

theorem axisMap_injective : Function.Injective (axisMap E e i) := by
  intro x y hxy
  have hh := congrArg (fun z : E => e z i) hxy
  simpa only [axisMap,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply,MonoidHom.mulSingle_apply,Pi.mulSingle_eq_same] using hh

/-- Support on the chosen actual coordinate, with all other coordinates1. -/
theorem axisMap_coordinates (t : T) :
    e (axisMap E e i t) = Pi.mulSingle i t := by
  exact e.apply_symm_apply _

theorem axis_normal : (axis E e i).Normal := by
  constructor
  rintro a ⟨t,rfl⟩ x
  refine ⟨(e x i)*t*(e x i)⁻¹,?_⟩
  apply e.injective
  funext j
  by_cases hj : j = i
  · subst j
    simp only [axisMap,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply,MonoidHom.mulSingle_apply,Pi.mulSingle_eq_same,
      map_mul,map_inv,Pi.mul_apply,Pi.inv_apply]
  · simp only [axisMap,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply,MonoidHom.mulSingle_apply,Pi.mulSingle_eq_of_ne hj,
      map_mul,map_inv,Pi.mul_apply,Pi.inv_apply,mul_one,mul_inv_cancel]

variable [Nontrivial T]

theorem axis_ne_bot : axis E e i ≠ ⊥ := by
  intro hbot
  obtain ⟨t,ht⟩ := exists_ne (1 : T)
  have hm : axisMap E e i t ∈ axis E e i := ⟨t,rfl⟩
  rw [hbot] at hm
  exact ht (axisMap_injective E e i ((Subgroup.mem_bot.mp hm).trans (map_one _).symm))

/-- The actual ambient conjugates of this one supported axis generateE.
This proves the orbit-generation fact, instead of assuming independent
coordinates or a transitive factor-permutation certificate. -/
theorem axis_normalClosure (hE : IsMinimalNormalSubgroup E) :
    Subgroup.normalClosure ((axis E e i).map E.subtype : Set G) = E :=
  MinimalNormalInternalFactorOrdinaryGenerators.normalClosure_eq E (axis E e i)
    hE (axis_ne_bot E e i)

theorem eq_top_of_axis_and_quotient (hE : IsMinimalNormalSubgroup E) [E.Normal]
    (H : Subgroup G) (haxis : (axis E e i).map E.subtype ≤ H)
    (hquot : H.map (QuotientGroup.mk' E) = ⊤) : H = ⊤ := by
  letI : E.Normal := hE.1
  letI : (axis E e i).Normal := axis_normal E e i
  exact NormalizerSharedOrdinaryGenerators.eq_top_of_map_eq_top E
    ((axis E e i).map E.subtype) H
    (MinimalNormalInternalFactorOrdinaryGenerators.le_normalizer E (axis E e i))
    (axis_normalClosure E e i hE) haxis hquot

variable [Finite G] [Finite T]

/-- Minimal ordinary generators of the actual coordinate group and of
the actual quotient, with their original marked union generatingG. -/
theorem exists_marked_generators (hE : IsMinimalNormalSubgroup E) :
    letI : E.Normal := hE.1
    ∃ s : Finset T, ∃ q : Finset (G ⧸ E),
      Subgroup.closure (s : Set T) = ⊤ ∧ s.card = MarkedC4.genRank T ∧
      Subgroup.closure (q : Set (G ⧸ E)) = ⊤ ∧ q.card = MarkedC4.genRank (G ⧸ E) ∧
      Subgroup.closure
        ((s.image (axisHom E e i) ∪ q.image Quotient.out : Finset G) : Set G) = ⊤ := by
  letI : E.Normal := hE.1
  obtain ⟨s,hs,hscl⟩ := MarkedC4.genRank_spec (G := T)
  obtain ⟨q,hq,hqcl⟩ := MarkedC4.genRank_spec (G := G ⧸ E)
  let F : Finset G := s.image (axisHom E e i) ∪ q.image Quotient.out
  let H : Subgroup G := Subgroup.closure (F : Set G)
  have haxis : (axis E e i).map E.subtype ≤ H := by
    rintro x ⟨a,⟨t,rfl⟩,rfl⟩
    have hm : t ∈ Subgroup.closure (s : Set T) := by rw [hscl]; trivial
    have hh := Subgroup.mem_map_of_mem (axisHom E e i) hm
    rw [MonoidHom.map_closure] at hh
    exact (Subgroup.closure_mono (by
      intro y hy
      simp only [F,Finset.coe_union,Finset.coe_image]
      exact Or.inl hy)) hh
  have hquot : H.map (QuotientGroup.mk' E) = ⊤ := by
    rw [eq_top_iff,←hqcl,Subgroup.closure_le]
    intro x hx
    refine ⟨Quotient.out x,Subgroup.subset_closure ?_,QuotientGroup.out_eq' x⟩
    simp only [F,Finset.coe_union,Finset.coe_image]
    exact Or.inr ⟨x,hx,rfl⟩
  exact ⟨s,q,hscl,hs,hqcl,hq,eq_top_of_axis_and_quotient E e i hE H haxis hquot⟩

include e i in
theorem genRank_le (hE : IsMinimalNormalSubgroup E) :
    letI : E.Normal := hE.1
    MarkedC4.genRank G ≤ MarkedC4.genRank T + MarkedC4.genRank (G ⧸ E) := by
  letI : E.Normal := hE.1
  obtain ⟨s,q,_,hs,_,hq,hgen⟩ := exists_marked_generators E e i hE
  have hh := MarkedC4.genRank_le hgen
  calc
    MarkedC4.genRank G ≤
        (s.image (axisHom E e i) ∪ q.image Quotient.out : Finset G).card := hh
    _ ≤ (s.image (axisHom E e i)).card+(q.image Quotient.out).card := Finset.card_union_le _ _
    _ ≤ s.card+q.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = MarkedC4.genRank T+MarkedC4.genRank (G ⧸ E) := by rw [hs,hq]

end SymmetricSubgroupAsymptotics.MinimalNormalIsotypicRelativeOrdinaryGenerators
