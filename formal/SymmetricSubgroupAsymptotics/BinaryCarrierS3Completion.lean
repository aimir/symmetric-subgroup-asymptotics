import SymmetricSubgroupAsymptotics.BinaryCarrierS3Decay
import SymmetricSubgroupAsymptotics.BinaryCarrierS3Union

/-! Complete positive-support S3 sector in the original thirteen-colour
carrier alphabet. The family consists of actual subgroups of the original
odd point set. All critical profiles, carrier multiplicities, physical
charts and parameter bins are included. Its bound has no counting input.
This finite-alphabet theorem does not assert coverage of all odd actions.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierS3Completion

abbrev Family (N : ℕ) := BinaryCarrierS3Union.Family N (fun _ _ => True)

/-- The exact S3 model contraction, original normalizer six, complete
weighted mixture, and cubic parameter cost are all installed. -/
theorem eventually_card_div_benchmark_le :
    ∀ᶠ N : ℕ in Filter.atTop,
      (Nat.card (Family N) : ℝ) / exactBenchmark (2*N+1) ≤
        (2 : ℝ)^(-(29/2980864)*(N : ℝ)) := by
  have hbin : ∀ᶠ N : ℕ in Filter.atTop,
      ∀ b : BinaryCarrierS3Union.bins N (fun _ _ => True),
        (Nat.card (BinaryCarrierS3Physical.PhysicalFamily
          (N-(2*b.1.1+4*b.1.2+1)) b.1.1 b.1.2 (Fin (2*N+1))) : ℝ) /
            exactBenchmark (2*N+1) ≤
              ((N : ℝ)+1) * (2 : ℝ)^(-(29/1490432)*(N : ℝ)) := by
    filter_upwards [BinaryCarrierS3Decay.eventually_physical_card_div_le] with N hN
    intro b
    exact hN _ _ _ (BinaryCarrierS3Union.bin_degree N (fun _ _ => True) b)
      (BinaryCarrierS3Union.bin_properties N (fun _ _ => True) b).1
  have h := BinaryCarrierS3Union.eventually_card_div_benchmark_le
    (fun _ _ _ => True) (29/1490432) (by norm_num) hbin
  norm_num only [show (29/1490432 : ℝ)/2 = 29/2980864 by norm_num] at h
  exact h

end SymmetricSubgroupAsymptotics.BinaryCarrierS3Completion
