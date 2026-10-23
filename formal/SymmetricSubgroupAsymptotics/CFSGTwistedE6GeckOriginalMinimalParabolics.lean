import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalUpperNormalizer
import SymmetricSubgroupAsymptotics.CFSGSurjectiveMinimalOvergroups

/-! The four displayed parabolics are exactly the minimal overgroups of
the literal positive Sylow normalizer in the ORIGINAL twisted E6 group.
The actual original central-kernel theorem justifies the subgroup
correspondence; no automorphism of the original group is lifted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalMinimalParabolics
open CFSGTwistedE6GeckOriginalUpperNormalizer CFSGE6GeckGeneratedParabolics
open CFSGTwistedE6GeckOriginalProjection CFSGTwistedE6GeckRelativeRootGenerated
open CFSGSurjectiveMinimalOvergroups CFSGSerreOrdinaryTwists

theorem original_upper_lt_simpleParabolic (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (a : Fin 4) :
    Subgroup.normalizer (originalPositiveSylow q : Set (CFSG.Models.TwistedE6 q))<
      originalSimpleParabolic q a := by
  have hh := map_lt_map_of_kernel_le (generatedToOriginal q)
    (original_kernel_le_upperGenerated q)
    (upperGenerated_lt_parabolicGenerated (q.Extension 2) (definingFieldAutomorphism q 2) a)
  rwa [upperGenerated_map_original] at hh

theorem original_simpleParabolic_minimal (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (a : Fin 4)
    (H : Subgroup (CFSG.Models.TwistedE6 q))
    (hBH : Subgroup.normalizer (originalPositiveSylow q : Set (CFSG.Models.TwistedE6 q))<H)
    (hHP : H≤originalSimpleParabolic q a) : H=originalSimpleParabolic q a := by
  have hh := map_minimal_overgroup (generatedToOriginal q) (generatedToOriginal_surjective q)
    (original_kernel_le_upperGenerated q)
    (upperGenerated_lt_parabolicGenerated (q.Extension 2) (definingFieldAutomorphism q 2) a)
    (parabolicGenerated_minimal (q.Extension 2) (definingFieldAutomorphism q 2) a)
  rw [upperGenerated_map_original] at hh
  exact hh H hBH hHP

theorem original_minimal_overgroup_eq_simpleParabolic (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (H : Subgroup (CFSG.Models.TwistedE6 q))
    (hBH : Subgroup.normalizer (originalPositiveSylow q : Set (CFSG.Models.TwistedE6 q))<H)
    (hmin : ∀M : Subgroup (CFSG.Models.TwistedE6 q),
      Subgroup.normalizer (originalPositiveSylow q : Set (CFSG.Models.TwistedE6 q))<M→M≤H→M=H) :
    ∃a : Fin 4,H=originalSimpleParabolic q a := by
  apply minimal_overgroup_family_surjective (generatedToOriginal q) (generatedToOriginal_surjective q)
    (original_kernel_le_upperGenerated q)
    (parabolicGenerated (q.Extension 2) (definingFieldAutomorphism q 2))
  · intro M hBM hminimal
    obtain ⟨a,ha⟩ := exists_parabolicGenerated_le (q.Extension 2)
      (definingFieldAutomorphism q 2) M hBM
    exact ⟨a,(hminimal _ (upperGenerated_lt_parabolicGenerated
      (q.Extension 2) (definingFieldAutomorphism q 2) a) ha).symm⟩
  · rwa [upperGenerated_map_original]
  · simpa only [upperGenerated_map_original] using hmin

theorem originalSimpleParabolic_injective (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] : Function.Injective (originalSimpleParabolic q) :=
  map_family_injective (generatedToOriginal q) (original_kernel_le_upperGenerated q)
    (parabolicGenerated (q.Extension 2) (definingFieldAutomorphism q 2))
    (fun a=>(upperGenerated_lt_parabolicGenerated
      (q.Extension 2) (definingFieldAutomorphism q 2) a).le)
    (parabolicGenerated_injective (q.Extension 2) (definingFieldAutomorphism q 2))

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalMinimalParabolics
