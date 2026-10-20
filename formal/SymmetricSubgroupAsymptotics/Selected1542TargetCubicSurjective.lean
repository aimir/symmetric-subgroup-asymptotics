import SymmetricSubgroupAsymptotics.Selected1542TargetAlternatingCoordinates
import SymmetricSubgroupAsymptotics.ActualRepeatedAlternatingCentralCoordinates

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
open ActualRepeatedAlternatingCentralCoordinates

private theorem generator_cubic_witness : ∃ p : Fin 3,
    NaturalA4ScalarFourHead.top (alternatingGenerator 0 0)^p.val=
      Multiplicative.ofAdd (1 : ZMod 3) := by decide +kernel

private theorem cubic_powers : ∀ t : CyclicThree,
    (Multiplicative.ofAdd (1 : ZMod 3))^t.toAdd.val=t := by decide +kernel

theorem target_top_surjective : Function.Surjective (top targetAlternating 0) := by
  obtain ⟨p,hp⟩ := generator_cubic_witness
  let g : literalTarget := (targetSource 0)^p.val
  have hs : top targetAlternating 0 (targetSource 0)=
      NaturalA4ScalarFourHead.top (alternatingGenerator 0 0) := by
    change NaturalA4ScalarFourHead.top (targetAlternating (targetSource 0) 0)=_
    rw [targetAlternating_generator]
  have hg : top targetAlternating 0 g=Multiplicative.ofAdd (1 : ZMod 3) := by
    change top targetAlternating 0 ((targetSource 0)^p.val)=_
    rw [map_pow,hs]
    exact hp
  intro t
  refine ⟨g^t.toAdd.val,?_⟩
  rw [map_pow,hg]
  exact cubic_powers t

end SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
