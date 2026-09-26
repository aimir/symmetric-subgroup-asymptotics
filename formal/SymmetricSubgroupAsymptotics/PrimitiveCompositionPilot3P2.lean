import SymmetricSubgroupAsymptotics.FiniteGeneratorCompositionWitness
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.Tactic.FinCases

/-! A small original-action pilot for the committed primitive degree-3,
index-2 record. Source image lists are [2,3,1] and [2,1,3]. The recorded
descending composition chain has generator lists [[1,3,2],[2,3,1]],
[[2,3,1]], [[1,2,3]]. We reverse that literal chain, retaining its actual
subgroups in the original generator closure. Only 1, 3 and 6 sparse rows
are checked; no quotient multiplication table or catalogue completeness
is assumed. All finite proof checks use the kernel.

Data locator: certificates/data/primitive_rank.jsonl.gz, action row with
catalogue=primitive, degree=3, index=2 (JSONL line 7263).
Uncompressed line SHA256 (including newline):
278d50e398cba7c8a293cacff74f5662d83320a3cb9f6b4182f9b23e16585461.
The source below proves its literal permutation facts independently of
that locator or any GAP order/normality/primitive assertions. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveCompositionPilot3P2

private def sourceCycle : Equiv.Perm (Fin 3) where
  toFun x := (#[1, 2, 0] : Array (Fin 3))[x.val]!
  invFun x := (#[2, 0, 1] : Array (Fin 3))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def sourceSwap : Equiv.Perm (Fin 3) where
  toFun x := (#[1, 0, 2] : Array (Fin 3))[x.val]!
  invFun x := (#[1, 0, 2] : Array (Fin 3))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Original source generators, in the committed record's order. -/
def sourceGenerators (j : Fin 2) : Equiv.Perm (Fin 3) :=
  if j.val = 0 then sourceCycle else sourceSwap

abbrev Original := Subgroup.closure (Set.range sourceGenerators)

private instance originalInhabited : Inhabited Original := ⟨1⟩

def originalGenerators (j : Fin 2) : Original :=
  ⟨sourceGenerators j, Subgroup.subset_closure (Set.mem_range_self j)⟩

theorem originalGenerators_full : Subgroup.closure (Set.range originalGenerators) = ⊤ :=
  binaryNormal_full_generators_of_equiv sourceGenerators originalGenerators
    (MulEquiv.refl _) (fun _ => rfl)

private def a : Original := originalGenerators 0
private def b : Original := originalGenerators 1
/-- This actual source word is the recorded permutation [1,3,2]. -/
private def u : Original := a * b * a⁻¹

private def trivialGenerators : Fin 1 → Original := fun _ => 1
private def ternaryGenerators : Fin 1 → Original := fun _ => a
private def topGenerators (j : Fin 2) : Original := if j.val = 0 then u else a

private def trivialCayley : FiniteCayleyCertificate trivialGenerators 1 where
  elements _ := 1
  identity := 0
  identity_eq := rfl
  next _ _ := 0
  next_eq := by decide +kernel
  words _ := []
  words_eq := by decide +kernel

private def ternaryCayley : FiniteCayleyCertificate ternaryGenerators 3 where
  elements i := (#[1, a, a * a] : Array Original)[i.val]!
  identity := 0
  identity_eq := rfl
  next i _ := (#[1, 2, 0] : Array (Fin 3))[i.val]!
  next_eq := by decide +kernel
  words i := (#[[], [0], [0, 0]] : Array (List (Fin 1)))[i.val]!
  words_eq := by decide +kernel

private def topCayley : FiniteCayleyCertificate topGenerators 6 where
  elements i := (#[1, a, a * a, u, a * u, a * a * u] : Array Original)[i.val]!
  identity := 0
  identity_eq := rfl
  next i j := if j.val = 0 then (#[3, 4, 5, 0, 1, 2] : Array (Fin 6))[i.val]!
    else (#[1, 2, 0, 5, 3, 4] : Array (Fin 6))[i.val]!
  next_eq := by decide +kernel
  words i := (#[[], [1], [1, 1], [0], [1, 0], [1, 1, 0]] :
    Array (List (Fin 2)))[i.val]!
  words_eq := by decide +kernel

private def inclusion0 : BinaryNormalGeneratorWords trivialGenerators ternaryGenerators where
  words _ := []
  equations := by decide +kernel

private def inclusion1 : BinaryNormalGeneratorWords ternaryGenerators topGenerators where
  words _ := [1]
  equations := by decide +kernel

private def conjugates0 : BinaryNormalGeneratorWords
    (fun ij : Fin 1 × Fin 1 => ternaryGenerators ij.1 * trivialGenerators ij.2 *
      (ternaryGenerators ij.1)⁻¹) trivialGenerators where
  words _ := []
  equations := by decide +kernel

private def conjugates1 : BinaryNormalGeneratorWords
    (fun ij : Fin 2 × Fin 1 => topGenerators ij.1 * ternaryGenerators ij.2 *
      (topGenerators ij.1)⁻¹) ternaryGenerators where
  words ij := if ij.1.val = 0 then [0, 0] else [0]
  equations := by decide +kernel

/-- Both original source generators are words in the recorded top tuple. -/
private def originalInTop : BinaryNormalGeneratorWords originalGenerators topGenerators where
  words j := if j.val = 0 then [1] else [1, 1, 0, 1]
  equations := by decide +kernel

private theorem trivialGenerators_bot :
    Subgroup.closure (Set.range trivialGenerators) = ⊥ := by
  apply le_antisymm _ bot_le
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  exact Subgroup.one_mem _

private theorem topGenerators_full : Subgroup.closure (Set.range topGenerators) = ⊤ := by
  apply top_unique
  rw [← originalGenerators_full]
  exact originalInTop.closure_le

private def generatorCount : Fin 3 → ℕ :=
  Fin.cases 1 (Fin.cases 1 (fun _ => 2))

/-- These are exactly the recorded chain tuples, in ascending order. -/
def levelGenerators : (i : Fin 3) → Fin (generatorCount i) → Original :=
  Fin.cases trivialGenerators (Fin.cases ternaryGenerators (fun _ => topGenerators))

private def rowCount : Fin 3 → ℕ :=
  Fin.cases 1 (Fin.cases 3 (fun _ => 6))

private def levelCayley : ∀ i : Fin 3,
    FiniteCayleyCertificate (levelGenerators i) (rowCount i) :=
  Fin.cases trivialCayley (Fin.cases ternaryCayley (fun _ => topCayley))

/-- The sparse actual chain, with all group-theoretic evidence supplied. -/
def certificate : SparsePrimeCompositionCertificate Original where
  length := 2
  generatorCount := generatorCount
  generators := levelGenerators
  rowCount := rowCount
  cayley := levelCayley
  rows_injective := by
    intro i
    fin_cases i <;> decide +kernel
  inclusionWords :=
    Fin.cases inclusion0 (Fin.cases inclusion1 (fun i => Fin.elim0 i))
  conjugateWords :=
    Fin.cases conjugates0 (Fin.cases conjugates1 (fun i => Fin.elim0 i))
  edgeOrder i := if i.val = 0 then 3 else 2
  edgePrime := by decide +kernel
  cardRatio := by decide +kernel
  head := trivialGenerators_bot
  last := topGenerators_full

/-- Exact one-based source image lists from the committed record. -/
theorem sourceGenerator_images : ∀ j : Fin 2, ∀ x : Fin 3,
    (sourceGenerators j x).val + 1 =
      (((#[#[2, 3, 1], #[2, 1, 3]] : Array (Array ℕ))[j.val]!)[x.val]!) := by
  decide +kernel

/-- Exact one-based composition image lists from the committed record,
reversed once to give the ascending chain required by the adapter. -/
theorem compositionGenerator_images : ∀ i : Fin 3,
    ∀ j : Fin (generatorCount i), ∀ x : Fin 3,
    ((levelGenerators i j : Equiv.Perm (Fin 3)) x).val + 1 =
      ((((#[#[#[1, 2, 3]], #[#[2, 3, 1]], #[#[1, 3, 2], #[2, 3, 1]]] :
        Array (Array (Array ℕ)))[i.val]!)[j.val]!)[x.val]!) := by
  decide +kernel

theorem original_card : Nat.card Original = 6 := by
  have h := certificate.subgroup_card (Fin.last 2)
  change Nat.card (Subgroup.closure (Set.range topGenerators)) = 6 at h
  rw [topGenerators_full, Subgroup.card_top] at h
  exact h

/-- Transitivity is witnessed by powers of the actual original 3-cycle. -/
instance original_pretransitive : MulAction.IsPretransitive Original (Fin 3) :=
  ⟨fun x y => by
    have h : ∀ x y : Fin 3, ∃ k : Fin 3,
        ((a ^ k.val : Original) : Equiv.Perm (Fin 3)) x = y := by decide +kernel
    obtain ⟨k, hk⟩ := h x y
    exact ⟨a ^ k.val, hk⟩⟩

/-- Prime degree plus the proved original transitivity proves primitivity;
the catalogue locator is not a primitive-action premise. -/
instance original_preprimitive : MulAction.IsPreprimitive Original (Fin 3) :=
  MulAction.IsPreprimitive.of_prime_card (by
    simpa only [Nat.card_fin] using (by decide : Nat.Prime 3))

theorem ternaryCount_eq_one : certificate.ternaryCount = 1 := by decide +kernel

theorem chosen_chief_weight_le_one (c : ActualChiefSeries Original) :
    actualChiefSeriesTernaryWeight c ≤ 1 := by
  simpa only [ternaryCount_eq_one] using certificate.chiefWeight_le c

theorem chosen_chief_weight_le_degree_third (c : ActualChiefSeries Original) :
    actualChiefSeriesTernaryWeight c ≤ Nat.card (Fin 3) / 3 := by
  simpa only [Nat.card_fin, Nat.reduceDiv] using chosen_chief_weight_le_one c

theorem exists_chief_weight_le_one :
    ∃ c : ActualChiefSeries Original, actualChiefSeriesTernaryWeight c ≤ 1 := by
  simpa only [ternaryCount_eq_one] using certificate.exists_chiefSeries_le

end SymmetricSubgroupAsymptotics.PrimitiveCompositionPilot3P2
