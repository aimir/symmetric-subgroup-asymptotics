import SymmetricSubgroupAsymptotics.ActualWreathChiefHalfOrderBudget
import SymmetricSubgroupAsymptotics.InducedMinimumRealLogarithmic

/-! Characteristic-aware costs of an ACTUAL finite chief compression.
Each output charge retains its original prime, dimension, and least
induced capacity, with all five simultaneous proved estimates. The sum
of genuine simple-factor ranks is kept separately. Profiles are produced
from the actual ChiefCost proof, never assumed as numerical certificates. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualWreathCharacteristicChiefProfile
open PermutationalWreathProduct

structure ElementaryCharge (t : ℕ) where
  p : ℕ
  prime : p.Prime
  dimension : ℕ
  capacity : ℕ
  half : (capacity : ℝ) ≤ (dimension : ℝ) * t / 2
  logarithmic : (capacity : ℝ) ≤
    2 * (dimension : ℝ) * t / Real.sqrt (Real.logb 2 (t : ℝ))
  primeTo : ∀ q e : ℕ, q.Prime → q ≠ p → q ^ e ∣ t →
    (capacity : ℝ) ≤ (dimension : ℝ) * t / (q : ℝ) ^ e
  primary : ∀ e : ℕ, 1 ≤ e → p ^ e ∣ t →
    (capacity : ℝ) ≤ (dimension : ℝ) * t *
      Real.sqrt (2 / (3 * ((p : ℝ) - 1) * e))
  primePower : ∀ q e : ℕ, q.Prime → t = q ^ e →
    (capacity : ℝ) ≤ (dimension : ℝ) * t *
      ((e * (q - 1)).choose ((e * (q - 1)) / 2) : ℝ) /
        (2 : ℝ) ^ (e * (q - 1))

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
    [MulAction Q I] [FaithfulSMul Q I]

def actualCharge (S : ActualWreathCompressionState Q I)
    {D' : Type} [Group D'] (phi : S.D →* D')
    (C : ElementaryMinimalNormalChart phi.ker) (i : I)
    (hI : 2 ≤ Fintype.card I) : ElementaryCharge (Fintype.card I) where
  p := C.p
  prime := C.p_prime
  dimension := Module.finrank (ZMod C.p) C.V
  capacity := ActualWreathElementaryOrdinaryStep.layerCapacity S phi C i
  half := ActualWreathElementaryOrdinaryStep.layerCapacity_le_half S phi C i hI
  logarithmic := by
    have hi : 2 ≤ (S.topPointStabilizer i).index := by
      simpa only [S.topPointStabilizer_index i] using hI
    simpa only [ActualWreathElementaryOrdinaryStep.layerCapacity,
      S.topPointStabilizer_index i] using
      InducedMinimumUniformCapacity.logarithmic_real (S.topPointStabilizer i)
        (ActualWreathAffineCapacity.localRepresentation S phi C i) hi
  primeTo q e hq hqp hd := by
    have hd' : q ^ e ∣ (S.topPointStabilizer i).index := by
      simpa only [S.topPointStabilizer_index i] using hd
    simpa only [ActualWreathElementaryOrdinaryStep.layerCapacity,
      S.topPointStabilizer_index i] using
      InducedMinimumUniformCapacity.primeTo (S.topPointStabilizer i)
        (ActualWreathAffineCapacity.localRepresentation S phi C i) q e hq hqp hd'
  primary e he hd := by
    have hd' : C.p ^ e ∣ (S.topPointStabilizer i).index := by
      simpa only [S.topPointStabilizer_index i] using hd
    simpa only [ActualWreathElementaryOrdinaryStep.layerCapacity,
      S.topPointStabilizer_index i] using
      InducedMinimumUniformCapacity.primary (S.topPointStabilizer i)
        (ActualWreathAffineCapacity.localRepresentation S phi C i) e he hd'
  primePower q e hq ht := by
    have ht' : (S.topPointStabilizer i).index = q ^ e := by
      simpa only [S.topPointStabilizer_index i] using ht
    simpa only [ActualWreathElementaryOrdinaryStep.layerCapacity,
      S.topPointStabilizer_index i] using
      InducedMinimumUniformCapacity.primePower (S.topPointStabilizer i)
        (ActualWreathAffineCapacity.localRepresentation S phi C i) q e hq ht'

structure Profile (t cost localOrder : ℕ) where
  charges : List (ElementaryCharge t)
  simpleRank : ℕ
  total : cost = (charges.map (·.capacity)).sum + simpleRank
  order_bound : (charges.map (fun c => c.p ^ c.dimension)).prod *
    2 ^ simpleRank ≤ localOrder

/-- The finite charge list is extracted from actual local edges. Its
prime dimensions and simple costs are not replaced by a total log-order. -/
theorem profile_of_chiefCost
    {i : I} {S : ActualWreathCompressionState Q I} {n : ℕ}
    (h : ActualWreathOrdinaryChiefRecurrence.ChiefCost i S n)
    (hI : 2 ≤ Fintype.card I) :
    Nonempty (Profile (Fintype.card I) n (Nat.card S.D)) := by
  induction h with
  | terminal S hD =>
      refine ⟨{ charges := [], simpleRank := 0, total := by simp, order_bound := ?_ }⟩
      simpa only [List.map_nil, List.prod_nil, pow_zero, one_mul] using
        (Nat.card_pos (α := S.D))
  | vanishing S D' phi hphi hmin hz n next ih =>
      obtain ⟨P⟩ := ih
      exact ⟨{
        charges := P.charges
        simpleRank := P.simpleRank
        total := P.total
        order_bound := P.order_bound.trans (Nat.card_le_card_of_surjective phi hphi) }⟩
  | elementary S D' phi hphi hmin C n next ih =>
      obtain ⟨P⟩ := ih
      refine ⟨{
        charges := actualCharge S phi C i hI :: P.charges
        simpleRank := P.simpleRank
        total := ?_
        order_bound := ?_ }⟩
      · change ActualWreathElementaryOrdinaryStep.layerCapacity S phi C i + n =
          (ActualWreathElementaryOrdinaryStep.layerCapacity S phi C i +
            (P.charges.map (·.capacity)).sum) + P.simpleRank
        exact (congrArg
          (Nat.add (ActualWreathElementaryOrdinaryStep.layerCapacity S phi C i))
          P.total).trans (Nat.add_assoc _ _ _).symm
      · change (C.p ^ Module.finrank (ZMod C.p) C.V *
            (P.charges.map (fun c => c.p ^ c.dimension)).prod) *
          2 ^ P.simpleRank ≤ Nat.card S.D
        calc
          _ = C.p ^ Module.finrank (ZMod C.p) C.V *
              ((P.charges.map (fun c => c.p ^ c.dimension)).prod * 2 ^ P.simpleRank) :=
            Nat.mul_assoc _ _ _
          _ ≤ C.p ^ Module.finrank (ZMod C.p) C.V * Nat.card D' :=
            Nat.mul_le_mul_left _ P.order_bound
          _ = Nat.card phi.ker * Nat.card D' := by
            rw [ActualWreathChiefHalfOrderBudget.elementary_kernel_card phi C]
          _ = Nat.card S.D :=
            ActualWreathChiefHalfOrderBudget.card_kernel_mul_card_of_surjective phi hphi
  | nonabelian S D' phi hphi hmin hnc hne C j n next ih =>
      obtain ⟨P⟩ := ih
      refine ⟨{
        charges := P.charges
        simpleRank := MarkedC4.genRank (C.factor j) + P.simpleRank
        total := ?_
        order_bound := ?_ }⟩
      · have ht := P.total
        omega
      · calc
          _ = 2 ^ MarkedC4.genRank (C.factor j) *
              ((P.charges.map (fun c => c.p ^ c.dimension)).prod * 2 ^ P.simpleRank) := by
            rw [pow_add]
            ac_rfl
          _ ≤ Nat.card phi.ker * Nat.card D' :=
            Nat.mul_le_mul
              (ActualWreathChiefFactorOrder.two_pow_factor_genRank_le_local_kernel
                S.rho phi S.rho_injective C j) P.order_bound
          _ = Nat.card S.D :=
            ActualWreathChiefHalfOrderBudget.card_kernel_mul_card_of_surjective phi hphi

theorem exists_profile (S : ActualWreathCompressionState Q I)
    (i : I) (hI : 2 ≤ Fintype.card I) :
    ∃ n : ℕ, ActualWreathOrdinaryChiefRecurrence.ChiefCost i S n ∧
      Nonempty (Profile (Fintype.card I) n (Nat.card S.D)) := by
  obtain ⟨n, hn⟩ := ActualWreathOrdinaryChiefRecurrence.exists_chiefCost i S
  exact ⟨n, hn, profile_of_chiefCost hn hI⟩

end SymmetricSubgroupAsymptotics.ActualWreathCharacteristicChiefProfile
