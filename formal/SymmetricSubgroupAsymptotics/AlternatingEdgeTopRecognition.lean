import SymmetricSubgroupAsymptotics.AlternatingEdgeOriginalProjectorHeads

/-! Recognize an actual edge A4 image from containment and two original
word witnesses. Only the fixed four-point permutation action is finite. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AlternatingEdgeTopRecognition
open AlternatingEdgeOriginalProjectorHeads (Top)
open SymmetricFourTwelvePointSocles (edge)

private theorem edge_injective : Function.Injective edge := by decide +kernel

variable {U : Type} [Group U] (top : U →* Equiv.Perm (Fin 6))
    (hinside : ∀ u, ∃ p : Top, edge p.val=top u)
    (wa wb : U)
    (ha : top wa=edge FourPointAlternatingGeneratorCover.a)
    (hb : top wb=edge FourPointAlternatingGeneratorCover.b)

include ha hb in
private theorem edge_mem (p : Top) : edge p.val ∈ top.range := by
  have hA : FourPointAlternatingGeneratorCover.a ∈ top.range.comap edge := ⟨wa,ha⟩
  have hB : FourPointAlternatingGeneratorCover.b ∈ top.range.comap edge := ⟨wb,hb⟩
  exact FourPointAlternatingGeneratorCover.alternating_le (top.range.comap edge) hA hB p.property

include ha hb in
def hom : Top →* top.range where
  toFun p := ⟨edge p.val,edge_mem top wa wb ha hb p⟩
  map_one' := Subtype.ext (map_one edge)
  map_mul' p q := Subtype.ext (map_mul edge p.val q.val)

include hinside ha hb in
def equiv : Top ≃* top.range := MulEquiv.ofBijective (hom top wa wb ha hb) (by
  constructor
  · intro p q h
    exact Subtype.ext (edge_injective (congrArg Subtype.val h))
  · intro y
    obtain ⟨u,hu⟩ := y.property
    obtain ⟨p,hp⟩ := hinside u
    exact ⟨p,Subtype.ext (hp.trans hu)⟩)

include hinside ha hb in
theorem equiv_apply (p : Top) : (equiv top hinside wa wb ha hb p).val=edge p.val := rfl

end SymmetricSubgroupAsymptotics.AlternatingEdgeTopRecognition
