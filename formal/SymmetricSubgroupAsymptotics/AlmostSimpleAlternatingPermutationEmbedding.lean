import SymmetricSubgroupAsymptotics.CFSGAlternatingOuterBound
import SymmetricSubgroupAsymptotics.NormalSubgroupOuterEmbedding
import SymmetricSubgroupAsymptotics.AlmostSimpleIndexTwoSubnormalClasses

/-! The original almost-simple ambient group embeds into the actual
symmetric group when its normal simple subgroup is alternating of degree
other than six. The normal subgroup's original elements supply the
literal alternating permutations in the image. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AlmostSimpleAlternatingPermutationEmbedding
open CFSGAlternatingOuterAutomorphisms CFSGAlternatingOuterBound
open NormalSubgroupOuterEmbedding AlmostSimpleIndexTwoSubnormalClasses
variable {G : Type} [Group G] [Finite G]
variable (N : Subgroup G) [N.Normal]
variable (m : ℕ) (hm : 5 ≤ m) (hne : m ≠ 6)
variable (e : N ≃* alternatingGroup (Fin m))

def automorphismEquiv : Equiv.Perm (Fin m)≃*MulAut (alternatingGroup (Fin m)) :=
  MulEquiv.ofBijective (permutationConjugation m)
    ⟨permutationConjugation_injective m hm,
      MonoidHom.range_eq_top.mp (permutationConjugation_range_eq_top m hm hne)⟩

def ambientHom : G→*Equiv.Perm (Fin m) :=
  (automorphismEquiv m hm hne).symm.toMonoidHom.comp
    ((autCongr e).toMonoidHom.comp (MulAut.conjNormal (H:=N)))

theorem ambientHom_injective (hC:Subgroup.centralizer (N:Set G)=⊥) :
    Function.Injective (ambientHom N m hm hne e) :=
  (automorphismEquiv m hm hne).symm.injective.comp
    ((autCongr e).injective.comp (conjNormal_injective N hC))

theorem ambientHom_on_normal (n:N) : ambientHom N m hm hne e n=(e n).val := by
  apply (automorphismEquiv m hm hne).injective
  change (automorphismEquiv m hm hne)
    ((automorphismEquiv m hm hne).symm (autCongr e (MulAut.conjNormal (H:=N) n)))=_
  rw [MulEquiv.apply_symm_apply]
  change autCongr e (MulAut.conjNormal (H:=N) n)=permutationConjugation m (e n).val
  calc
    _=autCongr e (MulAut.conj n) := congrArg (autCongr e) MulAut.conjNormal_val
    _=MulAut.conj (e n) := autCongr_conj e n
    _=_ := MulAut.conjNormal_val.symm

theorem alternating_le_range : alternatingGroup (Fin m)≤(ambientHom N m hm hne e).range := by
  intro a ha
  refine ⟨(e.symm ⟨a,ha⟩).val,?_⟩
  exact (ambientHom_on_normal N m hm hne e (e.symm ⟨a,ha⟩)).trans
    (congrArg Subtype.val (e.apply_symm_apply ⟨a,ha⟩))

theorem range_eq_alternating_or_top : (ambientHom N m hm hne e).range=alternatingGroup (Fin m) ∨
    (ambientHom N m hm hne e).range=⊤ := by
  letI : Nontrivial (Fin m) := Finite.one_lt_card_iff_nontrivial.mp (by simp only [Nat.card_fin];omega)
  exact containing_simple_index_two _ _ alternatingGroup.index_eq_two (alternating_le_range N m hm hne e)

theorem subnormal_image (H:Subgroup G)(hH:H.IsSubnormal) :
    (H.map (ambientHom N m hm hne e)).IsSubnormal := by
  let f:=ambientHom N m hm hne e
  have hr:f.range.IsSubnormal := by
    rcases range_eq_alternating_or_top N m hm hne e with he|he
    · rw [he]
      exact Subgroup.Normal.isSubnormal inferInstance
    · rw [he]
      exact Subgroup.IsSubnormal.top
  have hi:((H.map f.rangeRestrict).map f.range.subtype).IsSubnormal :=
    (hH.map f.rangeRestrict_surjective).trans' hr
  simpa only [Subgroup.map_map,MonoidHom.subtype_comp_rangeRestrict] using hi

end SymmetricSubgroupAsymptotics.AlmostSimpleAlternatingPermutationEmbedding
