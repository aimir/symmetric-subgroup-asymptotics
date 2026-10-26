import SymmetricSubgroupAsymptotics.AlternatingSmallPartitionCompositionCapacity

/-! The exceptional alternating degree six uses the same literal
even/split partition fibres as degrees five and seven. Only positive
compositions of mass six are reduced; no group is enumerated. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.AlternatingSixPartitionClassCapacity
open AlternatingSmallPartitionCompositionCapacity

theorem even_six_card : (evenMenu 6).card=6 := by decide +kernel
theorem split_six_card : (splitMenu 6).card=1 := by decide +kernel

theorem alternating_six_class_card_le :
    Nat.card (ConjClasses (alternatingGroup (Fin 6)))≤7 := by
  simpa only [even_six_card,split_six_card,Nat.reduceAdd] using
    class_card_le_menus 6 (by decide)

end SymmetricSubgroupAsymptotics.AlternatingSixPartitionClassCapacity
