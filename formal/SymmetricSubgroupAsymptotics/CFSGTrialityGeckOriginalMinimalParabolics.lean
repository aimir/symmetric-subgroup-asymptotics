import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalUpperNormalizer
import SymmetricSubgroupAsymptotics.CFSGSurjectiveMinimalOvergroups

/-! The two displayed parabolics are exactly the minimal overgroups of
the literal positive Sylow normalizer in the ORIGINAL triality D4 group.
The actual original central-kernel theorem justifies the subgroup
correspondence; no automorphism of the original group is lifted. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalMinimalParabolics
open CFSGTrialityGeckOriginalUpperNormalizer CFSGTrialityGeckGeneratedParabolics
open CFSGTrialityGeckGeneratedOriginalProjection CFSGTrialityGeckRelativeRootGenerated
open CFSGSurjectiveMinimalOvergroups CFSGSerreOrdinaryTwists
open CFSGTrialityGeckOriginalRootFamily

theorem original_upper_lt_simpleParabolic (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (a : Bool) :
    Subgroup.normalizer (originalSylow q : Set (CFSG.Models.TrialityD4 q))<
      originalSimpleParabolic q a := by
  have hh := map_lt_map_of_kernel_le (generatedToOriginal q)
    (original_kernel_le_upperGenerated q)
    (upperGenerated_lt_parabolicGenerated (q.Extension 3) (definingFieldAutomorphism q 3) a)
  rwa [upperGenerated_map_original] at hh

theorem original_simpleParabolic_minimal (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (a : Bool)
    (H : Subgroup (CFSG.Models.TrialityD4 q))
    (hBH : Subgroup.normalizer (originalSylow q : Set (CFSG.Models.TrialityD4 q))<H)
    (hHP : H≤originalSimpleParabolic q a) : H=originalSimpleParabolic q a := by
  have hh := map_minimal_overgroup (generatedToOriginal q) (generatedToOriginal_surjective q)
    (original_kernel_le_upperGenerated q)
    (upperGenerated_lt_parabolicGenerated (q.Extension 3) (definingFieldAutomorphism q 3) a)
    (parabolicGenerated_minimal (q.Extension 3) (definingFieldAutomorphism q 3) a)
  rw [upperGenerated_map_original] at hh
  exact hh H hBH hHP

theorem original_minimal_overgroup_eq_simpleParabolic (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (H : Subgroup (CFSG.Models.TrialityD4 q))
    (hBH : Subgroup.normalizer (originalSylow q : Set (CFSG.Models.TrialityD4 q))<H)
    (hmin : ∀M : Subgroup (CFSG.Models.TrialityD4 q),
      Subgroup.normalizer (originalSylow q : Set (CFSG.Models.TrialityD4 q))<M→M≤H→M=H) :
    ∃a : Bool,H=originalSimpleParabolic q a := by
  apply minimal_overgroup_family_surjective (generatedToOriginal q) (generatedToOriginal_surjective q)
    (original_kernel_le_upperGenerated q)
    (parabolicGenerated (q.Extension 3) (definingFieldAutomorphism q 3))
  · intro M hBM hminimal
    obtain ⟨a,ha⟩ := exists_parabolicGenerated_le (q.Extension 3)
      (definingFieldAutomorphism q 3) M hBM
    exact ⟨a,(hminimal _ (upperGenerated_lt_parabolicGenerated
      (q.Extension 3) (definingFieldAutomorphism q 3) a) ha).symm⟩
  · rwa [upperGenerated_map_original]
  · simpa only [upperGenerated_map_original] using hmin

theorem originalSimpleParabolic_injective (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] : Function.Injective (originalSimpleParabolic q) :=
  map_family_injective (generatedToOriginal q) (original_kernel_le_upperGenerated q)
    (parabolicGenerated (q.Extension 3) (definingFieldAutomorphism q 3))
    (fun a=>(upperGenerated_lt_parabolicGenerated
      (q.Extension 3) (definingFieldAutomorphism q 3) a).le)
    (parabolicGenerated_injective (q.Extension 3) (definingFieldAutomorphism q 3))

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalMinimalParabolics
