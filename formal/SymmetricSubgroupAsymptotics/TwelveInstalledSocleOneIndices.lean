import SymmetricSubgroupAsymptotics.TwelveInstalledSocleOneSixPairSource

/-! Small scalar-index check for the installed actual normal families.
This computes only membership and their capacity indices, never a group
or a normal-subgroup census. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwelveInstalledSocleOneSixPairSource

theorem indices_eq : indices =
    ({0,3,4,16,18,28,30,42,44,54,71,72,93,130,131,132,174,175,176,177,
      230,233,299,300} : Finset (Fin 301)) := by
  decide +kernel

theorem indices_card : indices.card=24 := by
  rw [indices_eq]
  decide +kernel

end SymmetricSubgroupAsymptotics.TwelveInstalledSocleOneSixPairSource
