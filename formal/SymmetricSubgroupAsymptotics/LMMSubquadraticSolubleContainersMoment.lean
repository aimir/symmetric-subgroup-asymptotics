import SymmetricSubgroupAsymptotics.LMMSubquadraticSolubleContainers
import SymmetricSubgroupAsymptotics.MarkedC4ConstructedLargeOrbitMoment

/-! The literal large-orbit relative encoding with the actual container
index cardinality. The retained labelled transitive count pays this index
once; no Pyber maximal-soluble conjugacy estimate is used. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.MarkedC4.LMMSubquadraticSolubleContainers
open LiteralSolubleOrbitContainers SolubleContainerCount SolubleContainerOrder
open LargeOrbitOrdinaryGeneration ActualLargeOrbitKernel

local instance (b : ℕ) : Fintype (Index (Fin b)) := Fintype.ofFinite _
local instance (b : ℕ) (i : Index (Fin b)) :
    Fintype (physicalContainer (Fin b) i) := Fintype.ofFinite _

theorem words_bound (hDixon : PublishedDixonOrder) (b l : ℕ) :
    (∑ i : Index (Fin b), (Fintype.card (physicalContainer (Fin b) i) : ℝ) ^ l) ≤
      (Nat.card (Index (Fin b)) : ℝ) * (2 : ℝ) ^ (2 * b * l) := by
  have ho (i : Index (Fin b)) :
      (Fintype.card (physicalContainer (Fin b) i) : ℝ) ≤ (2 : ℝ) ^ (2 * b) := by
    have h := physicalContainer_order (Fin b) hDixon i
    simp only [Fintype.card_fin, Nat.card_eq_fintype_card] at h
    exact_mod_cast h
  calc
    _ ≤ ∑ _i : Index (Fin b), ((2 : ℝ) ^ (2 * b)) ^ l :=
      Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (Nat.cast_nonneg _) (ho i) l)
    _ = _ := by simp [Nat.card_eq_fintype_card, pow_mul]

/-- The source, relative tuple, projection kernel and marked target are
the same literal objects as in the original constructed reduction. -/
theorem moment_le_of_relative_tuples
    (hDixon : PublishedDixonOrder)
    {C l b : ℕ} (hC : 2 ≤ C)
    (hrelative : ∀ G : SolublePermutationSubgroup b,
      ∃ t : Fin l → G.val,
        Subgroup.closure (Set.range t ∪ (projection G.val C).ker) = ⊤)
    (r : ℕ) :
    solubleMarkedC4Moment b r ≤
      (Nat.card (Index (Fin b)) : ℝ) * (2 : ℝ) ^ (2 * b * l) *
        (2 : ℝ) ^ (2 * r * l) * OrbitCutoffFamilies.solubleCount C b r := by
  let D := physicalContainer (Fin b)
  have hcover (G : SolublePermutationSubgroup b) : ∃ i, G.val ≤ D i := by
    letI : IsSolvable G.val := G.property
    exact cover (Fin b) G.val
  choose container hcontainer using hcover
  choose tuple htuple using hrelative
  let K : ∀ G : SolublePermutationSubgroup b, Subgroup G.val :=
    fun G => (projection G.val C).ker
  let P : Subgroup (PermutationGroup b) → Prop :=
    fun J => IsSolvable J ∧ OrbitCutoffFamilies.OrbitCutoff C J
  letI : Fintype (ContainerRelativeEncoding.Target P) :=
    inferInstanceAs (Fintype (OrbitCutoffFamilies.SolubleFamily C b))
  have hP (G : SolublePermutationSubgroup b) : P ((K G).map G.val.subtype) := by
    letI : IsSolvable G.val := G.property
    exact (solubleTarget G.val C hC).property
  have hs := ContainerRelativeEncoding.moment_le D
    (fun G : SolublePermutationSubgroup b => G.val) Subtype.val_injective
    container hcontainer K tuple htuple P hP r
  have ht : 0 ≤ OrbitCutoffFamilies.solubleCount C b r :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (words_bound hDixon b l)
      (by positivity : (0 : ℝ) ≤ 2 ^ (2 * r * l))) ht
  have hs' : solubleMarkedC4Moment b r ≤
      (∑ i : Index (Fin b), (Fintype.card (D i) : ℝ) ^ l) *
        (2 : ℝ) ^ (2 * r * l) * OrbitCutoffFamilies.solubleCount C b r := by
    simp only [← Nat.card_eq_fintype_card, solubleMarkedC4Moment,
      OrbitCutoffFamilies.solubleCount] at hs ⊢
    convert hs using 1
    congr 1
    apply Finset.sum_congr
    · ext z
      simp
    · intro z _
      rfl
  exact hs'.trans hm

theorem exists_cutoff_moment_le
    (h62 : PublishedProposition62) (hDixon : PublishedDixonOrder)
    (rate : ℝ) (hrate : 0 < rate) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ b r : ℕ,
      solubleMarkedC4Moment b r ≤
        (Nat.card (Index (Fin b)) : ℝ) *
          (2 : ℝ) ^ (2 * b * tupleLength rate b) *
          (2 : ℝ) ^ (2 * r * tupleLength rate b) *
          OrbitCutoffFamilies.solubleCount C b r := by
  obtain ⟨C, hC, ht⟩ := exists_cutoff_relative_tuples h62 rate hrate
  refine ⟨C, hC, ?_⟩
  intro b r
  apply moment_le_of_relative_tuples hDixon hC
  intro G
  letI : IsSolvable G.val := G.property
  exact ht b G.val

theorem code_cost_le (ε : ℝ) (rate : ℝ) (b r : ℕ)
    (hindex : (Nat.card (Index (Fin b)) : ℝ) ≤ (2 : ℝ) ^ (ε * (b : ℝ) ^ 2)) :
    (Nat.card (Index (Fin b)) : ℝ) *
        (2 : ℝ) ^ (2 * b * tupleLength rate b) *
        (2 : ℝ) ^ (2 * r * tupleLength rate b) ≤
      (2 : ℝ) ^ (ε * (b : ℝ) ^ 2 +
        2 * ((b : ℝ) + r) * tupleLength rate b) := by
  calc
    _ ≤ (2 : ℝ) ^ (ε * (b : ℝ) ^ 2) *
        (2 : ℝ) ^ (2 * b * tupleLength rate b) *
        (2 : ℝ) ^ (2 * r * tupleLength rate b) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hindex (by positivity)) (by positivity)
    _ = _ := by
      rw [← Real.rpow_natCast (2 : ℝ) (2 * b * tupleLength rate b),
        ← Real.rpow_natCast (2 : ℝ) (2 * r * tupleLength rate b),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      push_cast
      ring

/-- The former large-orbit marked bound with only the retained LMM count,
ordinary large-orbit generation and Dixon's ordinary order bound. -/
theorem marked_bound
    (h62 : PublishedProposition62)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hDixon : PublishedDixonOrder) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ᶠ b : ℕ in atTop, ∀ r : ℕ,
      solubleMarkedC4Moment b r ≤
        (2 : ℝ) ^ (δ * ((b : ℝ) + r) ^ 2) *
          OrbitCutoffFamilies.solubleCount C b r := by
  let rate : ℝ := δ / 8
  have hrate : 0 < rate := by dsimp [rate]; positivity
  obtain ⟨C, hC, hfinite⟩ := exists_cutoff_moment_le h62 hDixon rate hrate
  refine ⟨C, hC, ?_⟩
  filter_upwards [index_eventually_exp_bound hLMM (δ / 4) (by positivity),
    eventually_ge_atTop (⌈8 / δ⌉₊)] with b hmenu hb
  intro r
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hceil : (tupleLength rate b : ℝ) ≤ rate * b + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hrate.le hb0)).le
  have hb' : (8 : ℝ) / δ ≤ b :=
    (Nat.le_ceil _).trans (by exact_mod_cast hb)
  have hlarge : (8 : ℝ) ≤ δ * b := by
    simpa only [mul_comm] using (div_le_iff₀ hδ).mp hb'
  have hlinear : 2 * ((b : ℝ) + r) ≤ (δ / 4) * ((b : ℝ) + r) ^ 2 := by
    have hmul := mul_nonneg (show 0 ≤ δ * ((b : ℝ) + r) - 8 by nlinarith)
      (add_nonneg hb0 hr0)
    nlinarith
  have hquad : (b : ℝ) * ((b : ℝ) + r) ≤ ((b : ℝ) + r) ^ 2 := by
    nlinarith [mul_nonneg hr0 (add_nonneg hb0 hr0)]
  have herr : (δ / 4) * (b : ℝ) ^ 2 +
      2 * ((b : ℝ) + r) * tupleLength rate b ≤ δ * ((b : ℝ) + r) ^ 2 := by
    have ht := mul_le_mul_of_nonneg_left hceil
      (show 0 ≤ 2 * ((b : ℝ) + r) by positivity)
    have hs : (b : ℝ) ^ 2 ≤ ((b : ℝ) + r) ^ 2 := by nlinarith
    dsimp [rate] at ht
    nlinarith [mul_le_mul_of_nonneg_left hs (show 0 ≤ δ / 4 by positivity),
      mul_le_mul_of_nonneg_left hquad (show 0 ≤ δ / 4 by positivity)]
  calc
    solubleMarkedC4Moment b r ≤
        ((Nat.card (Index (Fin b)) : ℝ) *
          (2 : ℝ) ^ (2 * b * tupleLength rate b) *
          (2 : ℝ) ^ (2 * r * tupleLength rate b)) *
          OrbitCutoffFamilies.solubleCount C b r := hfinite b r
    _ ≤ (2 : ℝ) ^ ((δ / 4) * (b : ℝ) ^ 2 +
          2 * ((b : ℝ) + r) * tupleLength rate b) *
          OrbitCutoffFamilies.solubleCount C b r :=
      mul_le_mul_of_nonneg_right (code_cost_le (δ / 4) rate b r hmenu)
        (Finset.sum_nonneg (fun _ _ => by positivity))
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) herr)
      (Finset.sum_nonneg (fun _ _ => by positivity))

end SymmetricSubgroupAsymptotics.MarkedC4.LMMSubquadraticSolubleContainers
