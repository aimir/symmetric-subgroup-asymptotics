import SymmetricSubgroupAsymptotics.Selected1071TargetAlternatingCoordinates
import SymmetricSubgroupAsymptotics.Selected1071CentralBinaryCoordinates
import SymmetricSubgroupAsymptotics.ActualRepeatedAlternatingCentralCoordinates

/-! The original sixteen-point group itself is an actual nonsplit central
binary-two cover of synchronized threefold A4 coordinates. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1071QuotientGraph
open ActualRepeatedAlternatingCentralCoordinates

private theorem target_cubic_witness : ∃ p : Fin 3,
    NaturalA4ScalarFourHead.top (alternatingGenerator 1 0)^p.val=
      Multiplicative.ofAdd (1 : ZMod 3) := by decide +kernel

private theorem cubic_powers : ∀ t : CyclicThree,
    (Multiplicative.ofAdd (1 : ZMod 3))^t.toAdd.val=t := by decide +kernel

theorem original_top_surjective : Function.Surjective (top originalAlternating 0) := by
  obtain ⟨p,hp⟩ := target_cubic_witness
  obtain ⟨g,hg⟩ := originalToTarget_surjective ((targetSource 1)^p.val)
  have hgen : top originalAlternating 0 g=Multiplicative.ofAdd (1 : ZMod 3) := by
    change top targetAlternating 0 (originalToTarget g)=_
    rw [hg,map_pow]
    change NaturalA4ScalarFourHead.top (targetAlternating (targetSource 1) 0)^p.val=_
    rw [targetAlternating_generator]
    exact hp
  intro t
  refine ⟨g^t.toAdd.val,?_⟩
  rw [map_pow,hgen]
  exact cubic_powers t

private theorem original_kernel_central (z : originalAlternating.ker) (g : Original) :
    (z : Original)*g=g*(z : Original) := by
  have hz : (z : Original)∈originalKernel := by
    rw [← originalAlternating_ker]
    exact z.property
  obtain ⟨i,hi⟩ := hz
  apply Subtype.ext
  change ((z : Original) : Equiv.Perm (Fin 16))*g.val=
    g.val*((z : Original) : Equiv.Perm (Fin 16))
  rw [hi]
  exact kernel_central i g

/-- Actual original coordinates, with neither a split extension nor an
abstract group-order identification supplied as input. -/
def actualCentralRepeat : ScalarFourCentralTopCoordinates Original CyclicThree 2 3 :=
  coordinates originalAlternating 0
    (fun g i => targetAlternating_common (originalToTarget g) i)
    original_top_surjective original_kernel_central
    (centralBinaryCoordinates.comp
      (MulEquiv.subgroupCongr originalAlternating_ker).toMonoidHom)
    (centralBinaryCoordinates_injective.comp
      (MulEquiv.subgroupCongr originalAlternating_ker).injective)

end SymmetricSubgroupAsymptotics.Selected1071QuotientGraph
