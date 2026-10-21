import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryData
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T3

/-! Reversible eight-row enumeration of the ORIGINAL regular top. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistry

theorem groupElement_injective : Function.Injective groupElement := by
  have hc : ∀ i j : Fin 8,
      (∀ x : Fin 8, (groupElement i).val x = (groupElement j).val x) → i = j := by
    decide +kernel
  intro i j he
  exact hc i j (fun x => congrArg (fun g : H => g.val x) he)

def topRowEquiv : Fin 8 ≃ H :=
  Equiv.ofBijective groupElement ((Nat.bijective_iff_injective_and_card groupElement).mpr
    ⟨groupElement_injective, (Nat.card_fin 8).trans BinaryMenuCayley8T3.exact_card.symm⟩)

end SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistry
