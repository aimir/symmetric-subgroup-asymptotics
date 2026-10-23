import SymmetricSubgroupAsymptotics.CFSGFFourE6FixedIndexRepresentatives

/-! A selected integral matching of the 24 norm-pair roots with the
24 fixed roots. It exchanges the F4 relative root lengths and reverses
the pinned four-node order. This is only an index matching, not yet
covariance of either representation. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientRootMatching
open CFSGFFourE6NormPairRepresentatives CFSGFFourE6FixedIndexRepresentatives

def foldedWeight (v:Fin 6→ℤ) : Fin 4→ℤ := ![v 0+v 5,v 2+v 4,v 3,v 1]

def dualRoot (v:Fin 6→ℤ) : Fin 6→ℤ := ![v 1,v 0+v 5,v 3,v 2+v 4,v 3,v 1]

theorem dualRoot_mem : ∀v∈rootRepresentatives,dualRoot v∈fixedRootMenu := by decide +kernel

theorem dualRoot_injective_on : ∀v∈rootRepresentatives,∀w∈rootRepresentatives,
    dualRoot v=dualRoot w→v=w := by decide +kernel

theorem dualRoot_surjective_on : ∀w∈fixedRootMenu,∃v∈rootRepresentatives,dualRoot v=w :=
  by decide +kernel

theorem dualRoot_weight : ∀v∈rootRepresentatives,
    foldedWeight v=![dualRoot v 1,dualRoot v 3,dualRoot v 2,dualRoot v 0] :=
  by decide +kernel

noncomputable section

def rootDualMap (r:rootRepresentatives) : fixedRootMenu := ⟨dualRoot r.val,dualRoot_mem r.val r.property⟩

theorem rootDualMap_bijective : Function.Bijective rootDualMap := by
  constructor
  · intro r s he
    apply Subtype.ext
    exact dualRoot_injective_on r.val r.property s.val s.property (congrArg Subtype.val he)
  · intro w
    obtain ⟨v,hv,he⟩:=dualRoot_surjective_on w.val w.property
    exact ⟨⟨v,hv⟩,Subtype.ext he⟩

def rootDualEquiv : rootRepresentatives≃fixedRootMenu :=
  Equiv.ofBijective rootDualMap rootDualMap_bijective

theorem rootDualEquiv_val (r:rootRepresentatives) : (rootDualEquiv r).val=dualRoot r.val := rfl

def basisIndexDual : PairIndex≃FixedLabel := Equiv.sumCongr (Equiv.refl (Fin 2)) rootDualEquiv

theorem basisIndexDual_inl (i:Fin 2) : basisIndexDual (Sum.inl i)=Sum.inl i := rfl

theorem basisIndexDual_inr (r:rootRepresentatives) :
    basisIndexDual (Sum.inr r)=Sum.inr (rootDualEquiv r) := rfl

end
end SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientRootMatching
