import SymmetricSubgroupAsymptotics.BinaryOriginalWeightedDirectEntry

/-!
# Normalizer-natural partial direct selections

A finite boundary usually supplies direct entries only on the axes assigned
to the direct consumer.  The complementary axes must contribute zero to the
direct row, while the original action normalizer is still divided out before
the literal-axis sum.

This file packages that operation.  Active axes carry the complete
`BinaryOriginalWeightedDirectEntry`; inactive axes receive a genuine zero
coefficient.  The survival predicate is the normalizer-natural active-axis
predicate, so the zero coefficient is proved from an empty literal Goursat
fibre rather than imposed as a numerical assumption.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- A normalizer-natural subset of the literal normal axes, together with one
original-weight direct entry on every active axis. -/
structure BinaryOriginalWeightedPartialSelection {h : ℕ}
    (U : Subgroup (Equiv.Perm (Fin (2*h)))) where
  Active : Subgroup U → Prop
  active_natural : ∀ c : Subgroup.normalizer
      (U : Set (Equiv.Perm (Fin (2*h)))), ∀ N,
    Active N → Active (N.map (U.normalizerMonoidHom c).toMonoidHom)
  entry : ∀ N : {N : Subgroup U // N.Normal},
    Active N.1 → BinaryOriginalWeightedDirectEntry U N.1

namespace BinaryOriginalWeightedPartialSelection

variable {h : ℕ} {U : Subgroup (Equiv.Perm (Fin (2*h)))}
    (C : BinaryOriginalWeightedPartialSelection U)

/-- The exact local predicate used before original-normalizer division. -/
def predicate {b : ℕ}
    (H : Subgroup (U × Equiv.Perm (Fin b))) : Prop := C.Active H.goursatFst

theorem predicate_natural {b : ℕ} : FusionOrbitNatural (Z := Fin b) U C.predicate :=
  fusionOrbitNatural_axis U C.Active C.active_natural

/-- Active entries keep their exact shifted prefix; inactive axes are the
zero-prefix dummy terms of the masked row. -/
def prefixDegree (N : {N : Subgroup U // N.Normal}) : ℕ :=
  if hN : C.Active N.1 then (C.entry N hN).prefixDegree else 0

def markerHalf (N : {N : Subgroup U // N.Normal}) : ℕ :=
  if hN : C.Active N.1 then (C.entry N hN).markerHalf else 0

/-- The inactive coefficient is literally zero. -/
def liftConstant (N : {N : Subgroup U // N.Normal}) : ℝ :=
  if hN : C.Active N.1 then (C.entry N hN).liftConstant else 0

/-- A positive dummy gap lets the masked row use the common decay theorem;
it is multiplied by the zero inactive coefficient. -/
def gapParameter (N : {N : Subgroup U // N.Normal}) : ℝ :=
  if hN : C.Active N.1 then (C.entry N hN).gapParameter else 1

def momentWeight (N : {N : Subgroup U // N.Normal}) {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) : ℝ :=
  if hN : C.Active N.1 then (C.entry N hN).momentWeight J else 0

theorem prefix_eq_two_mul (N : {N : Subgroup U // N.Normal}) :
    C.prefixDegree N = 2*C.markerHalf N := by
  by_cases hN : C.Active N.1
  · simp only [prefixDegree, markerHalf, dif_pos hN]
    exact (C.entry N hN).prefix_eq_two_mul
  · simp only [prefixDegree, markerHalf, dif_neg hN, mul_zero]

theorem prefix_lt (hh : 0 < h) (N : {N : Subgroup U // N.Normal}) :
    C.prefixDegree N < 2*h := by
  by_cases hN : C.Active N.1
  · simpa only [prefixDegree, dif_pos hN] using (C.entry N hN).prefix_lt
  · simp only [prefixDegree, dif_neg hN]
    omega

theorem liftConstant_nonneg (N : {N : Subgroup U // N.Normal}) :
    0 ≤ C.liftConstant N := by
  by_cases hN : C.Active N.1
  · simpa only [liftConstant, dif_pos hN] using (C.entry N hN).liftConstant_nonneg
  · simp only [liftConstant, dif_neg hN]
    exact le_rfl

theorem gapParameter_pos (N : {N : Subgroup U // N.Normal}) :
    0 < C.gapParameter N := by
  by_cases hN : C.Active N.1
  · simpa only [gapParameter, dif_pos hN] using (C.entry N hN).gapParameter_pos
  · simp only [gapParameter, dif_neg hN, zero_lt_one]

theorem moment_le (N : {N : Subgroup U // N.Normal}) (b q : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)), C.momentWeight N J^q) ≤
      (subgroupCount (b+q*C.prefixDegree N) : ℝ) := by
  by_cases hN : C.Active N.1
  · simpa only [momentWeight, prefixDegree, dif_pos hN] using
      (C.entry N hN).moment_le b q
  · cases q with
    | zero =>
        rw [Nat.zero_mul, Nat.add_zero]
        simp [subgroupCount]
    | succ q =>
        simp only [momentWeight, prefixDegree, dif_neg hN, zero_pow (Nat.succ_ne_zero q),
          Finset.sum_const_zero, Nat.succ_mul]
        exact_mod_cast Nat.zero_le (subgroupCount b)

/-- The inactive literal quotient fibre is empty because its decoded
Goursat axis is exactly the supplied normal. -/
theorem survivingEpiCount_eq_zero_of_inactive {b : ℕ}
    (N : {N : Subgroup U // N.Normal}) (hN : ¬ C.Active N.1)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount U C.predicate N J = 0 := by
  let F := {β : GroupEpimorphism J (U ⧸ N.1) //
    C.predicate (fusionFullGoursatEncode N J β).1}
  letI : IsEmpty F := ⟨fun β => hN (by
    have hactive := β.2
    simpa only [predicate, fusionFullGoursatEncode, fusionQuotientGraph_axis,
      QuotientGroup.ker_mk'] using hactive)⟩
  unfold fusionSurvivingEpiCount
  change (Nat.card F : ℝ) = 0
  rw [Nat.card_eq_zero.mpr (Or.inl inferInstance)]
  norm_num

theorem original_envelope {b : ℕ}
    (N : {N : Subgroup U // N.Normal})
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount U C.predicate N J ≤
      fusionLocalFactor b h (C.prefixDegree N) (C.liftConstant N)
        (C.gapParameter N) * C.momentWeight N J := by
  by_cases hN : C.Active N.1
  · simpa only [prefixDegree, liftConstant, gapParameter, momentWeight, dif_pos hN] using
      (C.entry N hN).original_envelope C.predicate J
  · rw [C.survivingEpiCount_eq_zero_of_inactive N hN J]
    simp only [liftConstant, momentWeight, dif_neg hN, mul_zero]
    exact le_rfl

/-- The exact shifted row of the active axes. -/
def directRow (n m : ℕ) : ℝ :=
  fusionPhysicalDirectRow (fun _ : Unit => h) (fun _ : Unit => U)
    (fun _ N => C.prefixDegree N) (fun _ N => C.liftConstant N)
    (fun _ N => C.gapParameter N) n m

theorem directRow_nonneg (n m : ℕ) : 0 ≤ C.directRow n m :=
  fusionPhysicalDirectRow_nonneg (fun _ : Unit => h) (fun _ : Unit => U)
    _ _ _ (fun _ N => C.liftConstant_nonneg N) n m

theorem directRow_forward (hh : 0 < h) {n m : ℕ} (hnm : n ≤ m) :
    C.directRow n m = 0 :=
  fusionPhysicalDirectRow_forward (fun _ : Unit => h) (fun _ : Unit => U)
    _ _ _ (fun _ N => C.prefix_lt hh N) hnm

/-- Any original family covered by this action and the active-axis predicate
obeys the exact masked direct recurrence. -/
theorem direct_recurrence (hh : 0 < h) (n : ℕ) (hn : 2*h ≤ n)
    (F : Set (Subgroup (Equiv.Perm (Fin n))))
    (hcover : ∀ H ∈ F,
      H ∈ FusionCanonicalFamily U hn C.predicate) :
    (Nat.card F : ℝ)/exactBenchmark n ≤
      ∑ m ∈ Finset.range n, C.directRow n m *
        ((subgroupCount m : ℝ)/exactBenchmark m) := by
  apply fusionPhysicalUnion_direct_recurrence
    (fun _ : Unit => h) (fun _ : Unit => U) n (fun _ => hn) F
    (fun _ => C.predicate) (fun _ => C.predicate_natural) (fun H hH => ⟨(),hcover H hH⟩)
    (fun _ N => C.prefixDegree N) (fun _ N => C.liftConstant N)
    (fun _ N => C.gapParameter N) (fun _ N J => C.momentWeight N J)
  · intro _ N
    exact C.prefix_lt hh N
  · intro _ N
    exact C.liftConstant_nonneg N
  · intro _ N J
    exact C.original_envelope N J
  · intro _ N
    simpa only [pow_one, one_mul] using C.moment_le N (n-2*h) 1

theorem directRow_decay (hh : 0 < h) :
    ∃ A κ : ℝ, 0 < A ∧ 0 < κ ∧ ∀ᶠ n : ℕ in atTop,
      ∑ m ∈ Finset.range n, C.directRow n m ≤ A*(2:ℝ)^(-κ*(n:ℝ)) := by
  apply fusionFiniteDirectRow_decay
    (fun j : FusionPhysicalMenuAxis (fun _ : Unit => h) (fun _ : Unit => U) => h)
    (fun j => C.prefixDegree j.2) (fun j => C.markerHalf j.2)
    (fun j => C.liftConstant j.2)
    (fun j => fusionPhysicalMenuDivisor (fun _ : Unit => h) (fun _ : Unit => U) j.1)
    (fun j => C.gapParameter j.2)
  · intro j
    exact C.prefix_lt hh j.2
  · intro j
    exact C.prefix_eq_two_mul j.2
  · intro j
    exact C.liftConstant_nonneg j.2
  · intro j
    exact fusionPhysicalMenuDivisor_pos (fun _ : Unit => h) (fun _ : Unit => U) j.1
  · intro j
    exact C.gapParameter_pos j.2

theorem directRow_contractive (hh : 0 < h) :
    ∀ᶠ n : ℕ in atTop, ∑ m ∈ Finset.range n, C.directRow n m ≤ 1/2 := by
  apply fusionFiniteDirectRow_contractive
    (fun j : FusionPhysicalMenuAxis (fun _ : Unit => h) (fun _ : Unit => U) => h)
    (fun j => C.prefixDegree j.2) (fun j => C.markerHalf j.2)
    (fun j => C.liftConstant j.2)
    (fun j => fusionPhysicalMenuDivisor (fun _ : Unit => h) (fun _ : Unit => U) j.1)
    (fun j => C.gapParameter j.2)
  · intro j
    exact C.prefix_lt hh j.2
  · intro j
    exact C.prefix_eq_two_mul j.2
  · intro j
    exact C.liftConstant_nonneg j.2
  · intro j
    exact fusionPhysicalMenuDivisor_pos (fun _ : Unit => h) (fun _ : Unit => U) j.1
  · intro j
    exact C.gapParameter_pos j.2

end BinaryOriginalWeightedPartialSelection
end SymmetricSubgroupAsymptotics

end
