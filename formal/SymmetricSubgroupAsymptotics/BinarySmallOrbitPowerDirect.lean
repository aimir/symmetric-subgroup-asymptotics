import SymmetricSubgroupAsymptotics.BinaryTransitivePowerBoundaryFusion
import SymmetricSubgroupAsymptotics.BinaryOrderCharacterDirectFusion
import SymmetricSubgroupAsymptotics.FusionPhysicalCharts

/-! Direct first-moment fusion for an actual small-order binary orbit of
one fixed power degree. The orbit and its full restriction image come from
an original point chart; the finite action subtype contains every literal
accepted image. No action catalogue or supplied physical cover is used.

For `k ≥ 4`, the degree is `2^k` and the order cap is `2^(2^k/2)`.
The original normalizer, all original normal axes, and all correlations
with the complement remain in the direct row. Contraction is at fixed `k`;
neither constants nor thresholds are asserted uniformly in growing `k`.
The counting theorem retains the named character class-count input.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open Filter

namespace SymmetricSubgroupAsymptotics.BinarySmallOrbitPowerDirect

/-- The half-width used by the physical fusion API. -/
abbrev halfDegree (k : ℕ) : ℕ := 2^(k-1)

/-- Written as twice the half-width to preserve the literal point types
through the orbit/complement chart and the direct-kernel API. -/
abbrev degree (k : ℕ) : ℕ := 2*halfDegree k

theorem degree_eq_pow (k : ℕ) (hk : 1 ≤ k) : degree k = 2^k :=
  BinaryTransitivePowerBoundaryFusion.two_mul_half k hk

theorem halfDegree_eq_div (k : ℕ) (hk : 1 ≤ k) :
    halfDegree k = 2^k/2 := by
  rw [← degree_eq_pow k hk]
  exact (Nat.mul_div_right (halfDegree k) (by decide : 0 < 2)).symm

theorem halfDegree_pos (k : ℕ) : 0 < halfDegree k :=
  pow_pos (by decide : 0 < 2) _

/-- The literal full restriction image in the original chart. -/
def orbitAction {k n : ℕ} (H : Subgroup (Equiv.Perm (Fin n)))
    (e : Fin (degree k) ⊕ Fin (n-degree k) ≃ Fin n) :
    Subgroup (Equiv.Perm (Fin (degree k))) :=
  (fusionPhysicalBlockPullback (relabelSubgroup e.symm H)).map
    (MonoidHom.fst (Equiv.Perm (Fin (degree k)))
      (Equiv.Perm (Fin (n-degree k))))

/-- Transitivity of the full image makes the invariant block one actual
orbit. The order bound is on that original image, not a catalogue label. -/
structure OrbitChart (k : ℕ) {n : ℕ} (H : Subgroup (Equiv.Perm (Fin n))) where
  chart : Fin (degree k) ⊕ Fin (n-degree k) ≃ Fin n
  preserves : ∀ g ∈ relabelSubgroup chart.symm H,
    Set.MapsTo g
      (Set.range (Sum.inl : Fin (degree k) → Fin (degree k) ⊕ Fin (n-degree k)))
      (Set.range (Sum.inl : Fin (degree k) → Fin (degree k) ⊕ Fin (n-degree k)))
  binary : IsPGroup 2 (orbitAction H chart)
  transitive : MulAction.IsPretransitive (orbitAction H chart) (Fin (degree k))
  order_le : Nat.card (orbitAction H chart) ≤ 2^(halfDegree k)

/-- The full first block is one genuine orbit in these original chart
coordinates. No hypothesis that the complement splits is used. -/
theorem OrbitChart.orbit_eq {k n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))}
    (C : OrbitChart k H) (x : Fin (degree k)) :
    MulAction.orbit (relabelSubgroup C.chart.symm H) (Sum.inl x) =
      Set.range (Sum.inl : Fin (degree k) → Fin (degree k) ⊕ Fin (n-degree k)) := by
  let U := orbitAction H C.chart
  let K := relabelSubgroup C.chart.symm H
  letI : MulAction.IsPretransitive U (Fin (degree k)) := C.transitive
  have ht (a b : Fin (degree k)) : ∃ u : U,
      (u : Equiv.Perm (Fin (degree k))) a = b :=
    MulAction.exists_smul_eq U a b
  have hf := fusionDeletedModel_full U K rfl
  have hr := fusionDeletedModel_recovers U K C.preserves rfl
  have ho := fusionOrbitAction_orbit_eq U ht ⟨fusionDeletedModel U K, hf⟩ x
  exact (congrArg
    (fun L : Subgroup (Equiv.Perm (Fin (degree k) ⊕ Fin (n-degree k))) =>
      MulAction.orbit L (Sum.inl x)) hr).symm.trans ho

/-- An unmarked actual family: a subgroup belongs once, regardless of
the number of possible orbit choices or charts. -/
def physicalFamily (k n : ℕ) : Set (Subgroup (Equiv.Perm (Fin n))) :=
  {H | Nonempty (OrbitChart k H)}

/-- All literal transitive binary actions below the order cap on this
fixed original point set. Finiteness needs no enumeration of actions. -/
abbrev BoundaryAction (k : ℕ) :=
  {A : Subgroup (Equiv.Perm (Fin (degree k))) //
    IsPGroup 2 A ∧ MulAction.IsPretransitive A (Fin (degree k)) ∧
      Nat.card A ≤ 2^(halfDegree k)}

instance boundaryActionFintype (k : ℕ) : Fintype (BoundaryAction k) :=
  Fintype.ofFinite _

def boundaryAction {k : ℕ} (i : BoundaryAction k) :
    Subgroup (Equiv.Perm (Fin (degree k))) := i.1

theorem boundaryAction_isPGroup {k : ℕ} (i : BoundaryAction k) :
    IsPGroup 2 (boundaryAction i) := i.2.1

theorem boundaryAction_transitive {k : ℕ} (i : BoundaryAction k) :
    MulAction.IsPretransitive (boundaryAction i) (Fin (degree k)) := i.2.2.1

theorem boundaryAction_card_le {k : ℕ} (i : BoundaryAction k) :
    Nat.card (boundaryAction i) ≤ 2^(halfDegree k) := i.2.2.2

/-- Every original normal of every accepted literal action receives a
proved order/character certificate before any complement is chosen. -/
def boundarySelection (k : ℕ) (hk : 4 ≤ k) (i : BoundaryAction k) :
    BinaryOrderCharacterSelection (boundaryAction i) := by
  letI := boundaryAction_transitive i
  exact BinaryTransitivePowerBoundaryFusion.selectionOfDegree k hk
    (boundaryAction i) (degree_eq_pow k (by omega)) (boundaryAction_card_le i)

/-- The actual restriction image itself is the finite-menu entry. -/
theorem cover {k n : ℕ} (hn : degree k ≤ n)
    (H : Subgroup (Equiv.Perm (Fin n))) (hH : H ∈ physicalFamily k n) :
    ∃ i : BoundaryAction k,
      H ∈ FusionCanonicalFamily (h := halfDegree k) (boundaryAction i)
        hn (fun _ => True) := by
  obtain ⟨C⟩ := hH
  let i : BoundaryAction k :=
    ⟨orbitAction H C.chart, C.binary, C.transitive, C.order_le⟩
  refine ⟨i, ?_⟩
  exact fusionCanonicalFamily_of_chart (h := halfDegree k) (boundaryAction i)
    hn H C.chart C.preserves rfl (fun _ => True) trivial

/-- The complete original-action/normal row. Its target retains the
actual selected graph prefix. -/
def directRow (k : ℕ) (hk : 4 ≤ k) (n m : ℕ) : ℝ :=
  binaryOrderCharacterDirectRow (fun _ : BoundaryAction k => halfDegree k)
    boundaryAction (boundarySelection k hk) n m

/-- Physical coverage and naturality are proved for this actual family.
No coarse subgroup-count estimate or additive hot term is needed. -/
theorem direct_recurrence (k : ℕ) (hk : 4 ≤ k)
    (hMaroti : NilpotentConjugacyClassInput) (n : ℕ) (hn : degree k ≤ n) :
    (Nat.card (physicalFamily k n) : ℝ) / exactBenchmark n ≤
      ∑ m ∈ Finset.range n, directRow k hk n m *
        ((subgroupCount m : ℝ) / exactBenchmark m) :=
  binaryOrderCharacterSelection_direct_recurrence
    (fun _ : BoundaryAction k => halfDegree k) boundaryAction (boundarySelection k hk)
    hMaroti boundaryAction_isPGroup (fun _ => halfDegree_pos k)
    n (fun _ => hn) (physicalFamily k n) (fun _ _ => True)
    (fun _ _ _ _ => trivial) (cover hn)

theorem directRow_nonneg (k : ℕ) (hk : 4 ≤ k) (n m : ℕ) :
    0 ≤ directRow k hk n m :=
  binaryOrderCharacterDirectRow_nonneg
    (fun _ : BoundaryAction k => halfDegree k) boundaryAction (boundarySelection k hk) n m

theorem directRow_forward (k : ℕ) (hk : 4 ≤ k) {n m : ℕ} (hnm : n ≤ m) :
    directRow k hk n m = 0 :=
  binaryOrderCharacterDirectRow_forward
    (fun _ : BoundaryAction k => halfDegree k) boundaryAction (boundarySelection k hk)
    (fun _ => halfDegree_pos k) hnm

/-- At each fixed power degree the exact finite aggregate decays before
any bound is assumed on the complete ordinary subgroup sequence. -/
theorem directRow_decay (k : ℕ) (hk : 4 ≤ k) :
    ∃ A κ : ℝ, 0<A ∧ 0<κ ∧ ∀ᶠ n : ℕ in atTop,
      ∑ m ∈ Finset.range n, directRow k hk n m ≤ A*(2:ℝ)^(-κ*(n:ℝ)) :=
  binaryOrderCharacterDirectRow_decay
    (fun _ : BoundaryAction k => halfDegree k) boundaryAction (boundarySelection k hk)
    (fun _ => halfDegree_pos k)

theorem directRow_contractive (k : ℕ) (hk : 4 ≤ k) :
    ∀ᶠ n : ℕ in atTop,
      ∑ m ∈ Finset.range n, directRow k hk n m ≤ 1/2 :=
  binaryOrderCharacterDirectRow_contractive
    (fun _ : BoundaryAction k => halfDegree k) boundaryAction (boundarySelection k hk)
    (fun _ => halfDegree_pos k)

/-- Arbitrary exclusions restrict the same actual unmarked family.
They do not require any invariance of a chosen distinguished chart. -/
theorem filtered_direct_recurrence (k : ℕ) (hk : 4 ≤ k)
    (hMaroti : NilpotentConjugacyClassInput) (n : ℕ) (hn : degree k ≤ n)
    (R : Subgroup (Equiv.Perm (Fin n)) → Prop) :
    (Nat.card {H : physicalFamily k n // R H.1} : ℝ) / exactBenchmark n ≤
      ∑ m ∈ Finset.range n, directRow k hk n m *
        ((subgroupCount m : ℝ) / exactBenchmark m) := by
  have hc : Nat.card {H : physicalFamily k n // R H.1} ≤
      Nat.card (physicalFamily k n) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  exact (div_le_div_of_nonneg_right (by exact_mod_cast hc)
    (exactBenchmark_pos n).le).trans (direct_recurrence k hk hMaroti n hn)

end SymmetricSubgroupAsymptotics.BinarySmallOrbitPowerDirect

end
