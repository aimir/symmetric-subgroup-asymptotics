import SymmetricSubgroupAsymptotics.NormalImageQuotient
import SymmetricSubgroupAsymptotics.ChiefCompositionLength

/-! A normal section projects isomorphically past an actual normal kernel
when that kernel's intersection with its upper group lies in its lower
group. The result records the actual projected section, not only its order. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

/-- The projection preserves an actual normal section whose kernel is
already absent from that section. -/
def normalSectionProjectionEquiv
    {G : Type} [Group G] (E A B : Subgroup G) [E.Normal] [A.Normal] [B.Normal]
    (hAB : A≤B) (hinter : E⊓B≤A) :
    normalChainQuotient A B ≃*
      normalChainQuotient (A.map (QuotientGroup.mk' E)) (B.map (QuotientGroup.mk' E)) := by
  let pi := QuotientGroup.mk' E
  let PA := A.map pi
  let PB := B.map pi
  let lift : B→*PB := {
    toFun := fun b => ⟨pi b,⟨b,b.property,rfl⟩⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  let q := (normalChainMap PA PB).comp lift
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨b,hb⟩ := normalChainMap_surjective PA PB y
    obtain ⟨g,hg,hgb⟩ := b.property
    let gB : B := ⟨g,hg⟩
    have hgB : lift gB=b := Subtype.ext hgb
    exact ⟨gB,(congrArg (normalChainMap PA PB) hgB).trans hb⟩
  have hk : A=q.ker.map B.subtype := by
    ext g
    constructor
    · intro hg
      refine ⟨⟨g,hAB hg⟩,?_,rfl⟩
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff (pi g)).mpr ⟨g,hg,rfl⟩
    · rintro ⟨b,hb,rfl⟩
      have he : (QuotientGroup.mk' PA) (pi b)=1 := congrArg Subtype.val hb
      obtain ⟨a,ha,hab⟩ := (QuotientGroup.eq_one_iff (pi b)).mp he
      have heker : a⁻¹*(b : G)∈E := by
        apply (QuotientGroup.eq_one_iff (a⁻¹*(b : G))).mp
        change pi (a⁻¹*(b : G))=1
        simp only [map_mul,map_inv,hab,inv_mul_cancel]
      have hbker : a⁻¹*(b : G)∈B := B.mul_mem (B.inv_mem (hAB ha)) b.property
      have haA : a⁻¹*(b : G)∈A := hinter ⟨heker,hbker⟩
      have h := A.mul_mem ha haA
      simpa only [mul_inv_cancel_left] using h
  exact normalSectionQuotientEquiv B A q hq hk

/-- The actual relative index is unchanged by that section projection. -/
theorem normalSectionProjection_relIndex
    {G : Type} [Group G] [Finite G]
    (E A B : Subgroup G) [E.Normal] [A.Normal] [B.Normal]
    (hAB : A≤B) (hinter : E⊓B≤A) :
    A.relIndex B=(A.map (QuotientGroup.mk' E)).relIndex (B.map (QuotientGroup.mk' E)) := by
  rw [←normalChainQuotient_card A B,
    ←normalChainQuotient_card (A.map (QuotientGroup.mk' E)) (B.map (QuotientGroup.mk' E))]
  exact Nat.card_congr (normalSectionProjectionEquiv E A B hAB hinter).toEquiv

end SymmetricSubgroupAsymptotics
