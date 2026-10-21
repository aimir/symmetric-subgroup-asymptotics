import SymmetricSubgroupAsymptotics.SemisimpleNormalIntersectionPerfect
import SymmetricSubgroupAsymptotics.PrimeRelativeHeadChain

/-! An abelian original normal section sees no perfect intersection with
the actual semisimple normal subgroup. This is the semantic step needed to
project every abelian chief factor into the actual socle quotient. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics

/-- Every map from a perfect source to a commutative group is trivial,
without installing a replacement group structure on either carrier. -/
theorem perfect_hom_to_commutative_eq_one
    {P Q : Type} [Group P] [Group Q] [Group.IsPerfect P] [IsMulCommutative Q]
    (f : P→*Q) (p : P) : f p=1 := by
  letI : Group.IsPerfect f.range := Group.IsPerfect.range f
  letI : Subsingleton f.range := Group.IsPerfect.subsingleton_of_isMulCommutative
  exact congrArg Subtype.val (Subsingleton.elim (⟨f p,⟨p,rfl⟩⟩ : f.range) 1)

/-- For the literal abelian section B/A, the actual intersection E∩B is
already contained in A. No normal-series refinement or abstract factor
identification is supplied as a premise. -/
theorem semisimple_intersection_le_of_abelian_normalSection
    {G : Type} [Group G] {E : Subgroup G} (C : SemisimpleNormalChart E)
    (A B : Subgroup G) [A.Normal] [B.Normal]
    [IsMulCommutative (normalChainQuotient A B)] : E⊓B≤A := by
  let K := B.subgroupOf E
  letI : Group.IsPerfect K := C.normal_intersection_perfect B
  let incl : K→*B := {
    toFun := fun x => ⟨x.val.val,x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  let f : K→*normalChainQuotient A B := (normalChainMap A B).comp incl
  intro g hg
  let x : K := ⟨⟨g,hg.1⟩,hg.2⟩
  have h := perfect_hom_to_commutative_eq_one f x
  have he : (QuotientGroup.mk' A) g=1 := congrArg Subtype.val h
  exact (QuotientGroup.eq_one_iff g).mp he

end SymmetricSubgroupAsymptotics
