import SymmetricSubgroupAsymptotics.BinaryNativeOwnerPartition
import SymmetricSubgroupAsymptotics.BinaryFrontierTransport

/-!
# Native complete binary-error recurrence

The intrinsic four-owner partition is normalized here.  The positive S16
residual is the scalar; the wide-orbit, direct degree-eight, and direct
degree-sixteen owners contribute their already proved original-weight forward
rows.  Their finite sum remains exponentially small and is packaged in the
native interface consumed by the odd-marker transport.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryNativeRecurrence

open SymmetricSubgroupAsymptotics

def scalar (N : ℕ) : ℝ :=
  (Nat.card (BinaryS16DirectResidualPartition.DirectPositiveResidualFamily N) : ℝ) /
    exactBenchmark (2*N)

def kernel (N m : ℕ) : ℝ :=
  BinaryOriginalNoncriticalPhysical.directRow (2*N) m +
    BinaryDegreeEightNormalizerSaturatedDirect.directRow (2*N) m +
    BinaryDegree16NormalizerSaturatedDirect.directRow (2*N) m

theorem kernel_nonneg (N m : ℕ) : 0 ≤ kernel N m := by
  unfold kernel
  exact add_nonneg
    (add_nonneg (BinaryOriginalNoncriticalPhysical.directRow_nonneg _ _)
      (BinaryDegreeEightNormalizerSaturatedDirect.directRow_nonneg _ _))
    (BinaryDegree16NormalizerSaturatedDirect.directRow_nonneg _ _)

theorem kernel_forward {N m : ℕ} (h : 2*N ≤ m) : kernel N m = 0 := by
  rw [kernel, BinaryOriginalNoncriticalPhysical.directRow_forward h,
    BinaryDegreeEightNormalizerSaturatedDirect.directRow_forward h,
    BinaryDegree16NormalizerSaturatedDirect.directRow_forward h,
    add_zero,add_zero]

/-- Complete native recurrence before odd-marker transport. -/
theorem recurrence (N : ℕ) (hN : 1024≤N) :
    binaryErrorRatio N ≤ scalar N +
      ∑ m ∈ Finset.range (2*N), kernel N m * ordinarySubgroupRatio m := by
  have hcard := BinaryNativeOwnerPartition.card_le_owners N
  have hcardR : (Nat.card (NoncriticalBinarySubgroups N) : ℝ) ≤
      (Nat.card (BinaryOriginalNoncriticalPhysical.physicalFamily (2*N)) : ℝ) +
      (Nat.card (BinaryDegreeEightNormalizerSaturatedDirect.directFamily (2*N)) : ℝ) +
      (Nat.card (BinaryDegree16PhysicalAnalyticClosure.directFamily (2*N)) : ℝ) +
      (Nat.card (BinaryS16DirectResidualPartition.DirectPositiveResidualFamily N) : ℝ) := by
    exact_mod_cast hcard
  have hcover := div_le_div_of_nonneg_right hcardR (exactBenchmark_pos (2*N)).le
  have hw := BinaryOriginalNoncriticalPhysical.direct_recurrence (2*N) (by omega)
  have h8 := BinaryDegreeEightNormalizerSaturatedDirect.direct_recurrence (2*N) (by omega)
  have h16 := BinaryDegree16NormalizerSaturatedDirect.direct_recurrence (2*N) (by omega)
  have hrows := add_le_add (add_le_add hw h8) h16
  unfold binaryErrorRatio scalar
  calc
    (Nat.card (NoncriticalBinarySubgroups N) : ℝ) / exactBenchmark (2*N) ≤
        ((Nat.card (BinaryOriginalNoncriticalPhysical.physicalFamily (2*N)) : ℝ) +
        (Nat.card (BinaryDegreeEightNormalizerSaturatedDirect.directFamily (2*N)) : ℝ) +
        (Nat.card (BinaryDegree16PhysicalAnalyticClosure.directFamily (2*N)) : ℝ) +
        (Nat.card (BinaryS16DirectResidualPartition.DirectPositiveResidualFamily N) : ℝ)) /
          exactBenchmark (2*N) := hcover
    _ = ((Nat.card (BinaryOriginalNoncriticalPhysical.physicalFamily (2*N)) : ℝ) /
          exactBenchmark (2*N) +
        (Nat.card (BinaryDegreeEightNormalizerSaturatedDirect.directFamily (2*N)) : ℝ) /
          exactBenchmark (2*N) +
        (Nat.card (BinaryDegree16PhysicalAnalyticClosure.directFamily (2*N)) : ℝ) /
          exactBenchmark (2*N)) +
        (Nat.card (BinaryS16DirectResidualPartition.DirectPositiveResidualFamily N) : ℝ) /
          exactBenchmark (2*N) := by ring
    _ ≤ ((∑ m ∈ Finset.range (2*N),
          BinaryOriginalNoncriticalPhysical.directRow (2*N) m *
            ((subgroupCount m : ℝ)/exactBenchmark m)) +
        (∑ m ∈ Finset.range (2*N),
          BinaryDegreeEightNormalizerSaturatedDirect.directRow (2*N) m *
            ((subgroupCount m : ℝ)/exactBenchmark m)) +
        (∑ m ∈ Finset.range (2*N),
          BinaryDegree16NormalizerSaturatedDirect.directRow (2*N) m *
            ((subgroupCount m : ℝ)/exactBenchmark m))) +
        (Nat.card (BinaryS16DirectResidualPartition.DirectPositiveResidualFamily N) : ℝ) /
          exactBenchmark (2*N) := by
      have h := add_le_add_right hrows
        ((Nat.card (BinaryS16DirectResidualPartition.DirectPositiveResidualFamily N) : ℝ) /
          exactBenchmark (2*N))
      linarith
    _ = (Nat.card (BinaryS16DirectResidualPartition.DirectPositiveResidualFamily N) : ℝ) /
          exactBenchmark (2*N) +
        ∑ m ∈ Finset.range (2*N), kernel N m * ordinarySubgroupRatio m := by
      simp only [kernel,ordinarySubgroupRatio,add_mul,Finset.sum_add_distrib]
      ring

/-- The sum of the three original-weight rows has a uniform positive
exponential rate in half-degree. -/
theorem kernel_decay :
    ∃ C kappa : ℝ, 0<C ∧ 0<kappa ∧ ∀ᶠ N : ℕ in atTop,
      (∑ m ∈ Finset.range (2*N), kernel N m) ≤
        C*(2 : ℝ)^(-kappa*(N : ℝ)) := by
  obtain ⟨Cw,kw,hCw,hkw,hw⟩ := BinaryOriginalNoncriticalPhysical.directRow_decay
  obtain ⟨C8,k8,hC8,hk8,h8⟩ :=
    BinaryDegreeEightNormalizerSaturatedDirect.directRow_decay
  obtain ⟨C16,k16,hC16,hk16,h16⟩ :=
    BinaryDegree16NormalizerSaturatedDirect.directRow_decay
  let kappa := min kw (min k8 k16)
  have hkappa : 0<kappa := lt_min hkw (lt_min hk8 hk16)
  obtain ⟨Nw,hw'⟩ := Filter.eventually_atTop.mp hw
  obtain ⟨N8,h8'⟩ := Filter.eventually_atTop.mp h8
  obtain ⟨N16,h16'⟩ := Filter.eventually_atTop.mp h16
  refine ⟨Cw+C8+C16,kappa,by positivity,hkappa,?_⟩
  filter_upwards [eventually_ge_atTop (max Nw (max N8 N16))] with N hN
  have hwN := hw' (2*N) (by omega)
  have h8N := h8' (2*N) (by omega)
  have h16N := h16' (2*N) (by omega)
  have hpoww : (2 : ℝ)^(-kw*((2*N : ℕ) : ℝ)) ≤
      (2 : ℝ)^(-kappa*(N : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hk := min_le_left kw (min k8 k16)
    have hN0 : (0 : ℝ)≤N := by positivity
    push_cast
    nlinarith
  have hpow8 : (2 : ℝ)^(-k8*((2*N : ℕ) : ℝ)) ≤
      (2 : ℝ)^(-kappa*(N : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hk := (min_le_right kw (min k8 k16)).trans (min_le_left k8 k16)
    have hN0 : (0 : ℝ)≤N := by positivity
    push_cast
    nlinarith
  have hpow16 : (2 : ℝ)^(-k16*((2*N : ℕ) : ℝ)) ≤
      (2 : ℝ)^(-kappa*(N : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hk := (min_le_right kw (min k8 k16)).trans (min_le_right k8 k16)
    have hN0 : (0 : ℝ)≤N := by positivity
    push_cast
    nlinarith
  calc
    _ = (∑ m ∈ Finset.range (2*N),
          BinaryOriginalNoncriticalPhysical.directRow (2*N) m) +
        (∑ m ∈ Finset.range (2*N),
          BinaryDegreeEightNormalizerSaturatedDirect.directRow (2*N) m) +
        (∑ m ∈ Finset.range (2*N),
          BinaryDegree16NormalizerSaturatedDirect.directRow (2*N) m) := by
      simp only [kernel,Finset.sum_add_distrib]
    _ ≤ Cw*(2 : ℝ)^(-kw*((2*N : ℕ) : ℝ)) +
        C8*(2 : ℝ)^(-k8*((2*N : ℕ) : ℝ)) +
        C16*(2 : ℝ)^(-k16*((2*N : ℕ) : ℝ)) := by linarith
    _ ≤ Cw*(2 : ℝ)^(-kappa*(N : ℝ)) +
        C8*(2 : ℝ)^(-kappa*(N : ℝ)) +
        C16*(2 : ℝ)^(-kappa*(N : ℝ)) := by
      gcongr <;> positivity
    _ = _ := by ring

/-- Existence of the complete native certificate with the literal scalar and
kernel above. -/
theorem exists_rankForwardEstimate :
    ∃ B : BinaryFrontierTransport.RankForwardEstimate,
      B.scalar=scalar ∧ B.kernel=kernel := by
  obtain ⟨C,k,hC,hk,hrow⟩ := kernel_decay
  obtain ⟨Ns,hscalar⟩ := Filter.eventually_atTop.mp
    BinaryS16PositiveResidualEstimate.eventually_positiveResidual_card_div_benchmark_le
  obtain ⟨Nr,hrow'⟩ := Filter.eventually_atTop.mp hrow
  let threshold := max 1024 (max Ns Nr)
  let rho := min BinaryS16PositiveResidualEstimate.rate k
  have hrho : 0<rho := lt_min BinaryS16PositiveResidualEstimate.rate_pos hk
  refine ⟨{
    scalar := scalar
    kernel := kernel
    threshold := threshold
    rate := rho
    scalarConst := 1
    rowConst := C
    rate_pos := hrho
    scalarConst_pos := by norm_num
    rowConst_nonneg := hC.le
    kernel_nonneg := fun N _ m _ ↦ kernel_nonneg N m
    recurrence := ?_
    scalar_decay := ?_
    row_decay := ?_ },rfl,rfl⟩
  · intro N hN
    exact recurrence N ((le_max_left 1024 (max Ns Nr)).trans hN)
  · intro N hN
    have hNs : Ns≤N := (le_max_left Ns Nr).trans
      ((le_max_right 1024 (max Ns Nr)).trans hN)
    have hs := hscalar N hNs
    apply hs.trans
    simp only [one_mul]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hmin := min_le_left BinaryS16PositiveResidualEstimate.rate k
    have hN0 : (0 : ℝ)≤N := by positivity
    nlinarith
  · intro N hN
    have hNr : Nr≤N := (le_max_right Ns Nr).trans
      ((le_max_right 1024 (max Ns Nr)).trans hN)
    have hr := hrow' N hNr
    apply hr.trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hmin := min_le_right BinaryS16PositiveResidualEstimate.rate k
    have hN0 : (0 : ℝ)≤N := by positivity
    nlinarith

/-- The canonical native complete binary recurrence used by the rest of the
formal development. -/
noncomputable def rankForwardEstimate :
    BinaryFrontierTransport.RankForwardEstimate :=
  Classical.choose exists_rankForwardEstimate

@[simp] theorem rankForwardEstimate_scalar : rankForwardEstimate.scalar=scalar :=
  (Classical.choose_spec exists_rankForwardEstimate).1

@[simp] theorem rankForwardEstimate_kernel : rankForwardEstimate.kernel=kernel :=
  (Classical.choose_spec exists_rankForwardEstimate).2

end SymmetricSubgroupAsymptotics.BinaryNativeRecurrence
