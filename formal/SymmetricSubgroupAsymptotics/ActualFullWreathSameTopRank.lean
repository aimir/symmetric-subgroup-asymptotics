import SymmetricSubgroupAsymptotics.ActualFullWreathFamily
import SymmetricSubgroupAsymptotics.FinitePermutationalWreathInstance
import SymmetricSubgroupAsymptotics.FiniteGroupBinaryOrderGenerators
import SymmetricSubgroupAsymptotics.CoprimeNilpotentProductGenerators
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Same-top rank control. Only the BASE order is charged, while the
original top keeps its genuine ordinary rank. In particular there is no
logarithm of |Q| and no spurious t*log(t) term. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualFullWreathSameTopRank
open PermutationalWreathProduct

variable {C Q I : Type} [Group C] [Group Q] [MulAction Q I]
    [Finite C] [Finite Q] [Finite I]

private def kernelCoordinates (H : ActualFullWreathFamily.Family C Q I) :
    (rightHom.comp H.val.subtype).ker → (I → C) := fun n => n.val.val.left

private theorem kernelCoordinates_injective (H : ActualFullWreathFamily.Family C Q I) :
    Function.Injective (kernelCoordinates H) := by
  intro n m h
  apply Subtype.ext
  apply Subtype.ext
  apply PermutationalWreathProduct.ext
  · exact h
  · have hn : n.val.val.right=1 := n.property
    have hm : m.val.val.right=1 := m.property
    exact hn.trans hm.symm

theorem kernel_card_le (H : ActualFullWreathFamily.Family C Q I) :
    Nat.card (rightHom.comp H.val.subtype).ker≤Nat.card C ^ Nat.card I := by
  simpa only [Nat.card_fun] using Nat.card_le_card_of_injective
    (kernelCoordinates H) (kernelCoordinates_injective H)

theorem genRank_le (H : ActualFullWreathFamily.Family C Q I)
    (a : ℕ) (ha : Nat.card C≤2^a) :
    MarkedC4.genRank H.val≤Nat.card I*a+MarkedC4.genRank Q := by
  let pi : H.val →* Q := rightHom.comp H.val.subtype
  have hk : MarkedC4.genRank pi.ker≤a*Nat.card I :=
    FiniteGroupBinaryOrderGenerators.genRank_le_mul_of_card_le_pow pi.ker
      (Nat.card C) a (Nat.card I) ha (kernel_card_le H)
  have hq : MarkedC4.genRank (H.val ⧸ pi.ker)=MarkedC4.genRank Q :=
    CoprimeNilpotentProductGenerators.genRank_mulEquiv
      (QuotientGroup.quotientKerEquivOfSurjective pi (ActualFullWreathFamily.top_surjective H))
  have hh := MarkedC4.genRank_le_of_normal pi.ker
  rw [hq] at hh
  exact hh.trans (by simpa only [Nat.mul_comm a] using Nat.add_le_add_right hk (MarkedC4.genRank Q))

end SymmetricSubgroupAsymptotics.ActualFullWreathSameTopRank
