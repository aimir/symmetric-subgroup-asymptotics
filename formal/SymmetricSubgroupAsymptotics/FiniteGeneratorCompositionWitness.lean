import SymmetricSubgroupAsymptotics.FiniteGroupCertificates
import SymmetricSubgroupAsymptotics.FiniteGeneratorNormality
import SymmetricSubgroupAsymptotics.FiniteCompositionWitness

/-! Sparse certificates for soluble composition chains in an actual finite
group. Every level has its original generators and a checked sparse Cayley
certificate. Words certify consecutive inclusion and normality. Actual
cardinalities and displayed prime ratios determine the quotient indices.
No quotient multiplication table, group-order label, or catalogue coverage
is assumed. For permutation rows, instantiate G with the literal original
permutation subgroup, retaining its actual subtype elements throughout. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

/-- A finite ascending generator chain for the original ambient group.
Cayley rows must be injective, so their displayed counts are actual group
orders. The endpoint equations retain the trivial and full original group. -/
structure SparsePrimeCompositionCertificate (G : Type) [Group G] where
  length : ℕ
  generatorCount : Fin (length + 1) → ℕ
  generators : (i : Fin (length + 1)) → Fin (generatorCount i) → G
  rowCount : Fin (length + 1) → ℕ
  cayley : ∀ i, FiniteCayleyCertificate (generators i) (rowCount i)
  rows_injective : ∀ i, Function.Injective (cayley i).elements
  inclusionWords : ∀ i : Fin length,
    BinaryNormalGeneratorWords (generators i.castSucc) (generators i.succ)
  conjugateWords : ∀ i : Fin length,
    BinaryNormalGeneratorWords
      (fun jk : Fin (generatorCount i.succ) × Fin (generatorCount i.castSucc) =>
        generators i.succ jk.1 * generators i.castSucc jk.2 *
          (generators i.succ jk.1)⁻¹)
      (generators i.castSucc)
  edgeOrder : Fin length → ℕ
  edgePrime : ∀ i, (edgeOrder i).Prime
  cardRatio : ∀ i : Fin length, rowCount i.castSucc * edgeOrder i = rowCount i.succ
  head : Subgroup.closure (Set.range (generators 0)) = ⊥
  last : Subgroup.closure (Set.range (generators (Fin.last length))) = ⊤

namespace SparsePrimeCompositionCertificate

variable {G : Type} [Group G] (C : SparsePrimeCompositionCertificate G)

/-- Every level is the literal original generator closure. -/
def subgroup (i : Fin (C.length + 1)) : Subgroup G :=
  Subgroup.closure (Set.range (C.generators i))

theorem subgroup_card [Finite G] (i : Fin (C.length + 1)) :
    Nat.card (C.subgroup i) = C.rowCount i :=
  (C.cayley i).card_closure (C.rows_injective i)

theorem step_le (i : Fin C.length) : C.subgroup i.castSucc ≤ C.subgroup i.succ :=
  (C.inclusionWords i).closure_le

theorem step_normal [Finite G] (i : Fin C.length) :
    ((C.subgroup i.castSucc).subgroupOf (C.subgroup i.succ)).Normal :=
  generated_subgroupOf_normal_of_word_certificates
    (C.generators i.castSucc) (C.generators i.succ)
    (C.inclusionWords i) (C.conjugateWords i)

/-- Lagrange's theorem identifies the actual relative index with the
prime ratio. Neither the displayed ratio nor ambient order is taken on trust. -/
theorem step_index [Finite G] (i : Fin C.length) :
    (C.subgroup i.castSucc).relIndex (C.subgroup i.succ) = C.edgeOrder i := by
  have hmul : Nat.card (C.subgroup i.castSucc) *
      (C.subgroup i.castSucc).relIndex (C.subgroup i.succ) =
        Nat.card (C.subgroup i.succ) := by
    simpa only [Subgroup.relIndex_bot_left] using
      Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G)
        (C.subgroup i.castSucc) (C.subgroup i.succ) bot_le (C.step_le i)
  have hpos : C.rowCount i.castSucc ≠ 0 := by
    rw [← C.subgroup_card i.castSucc]
    exact (Nat.card_pos (α := C.subgroup i.castSucc)).ne'
  rw [C.subgroup_card i.castSucc, C.subgroup_card i.succ] at hmul
  exact mul_left_cancel₀ hpos (hmul.trans (C.cardRatio i).symm)

theorem step_lt [Finite G] (i : Fin C.length) :
    C.subgroup i.castSucc < C.subgroup i.succ := by
  apply lt_of_le_of_ne (C.step_le i)
  intro he
  have hi : (C.subgroup i.castSucc).relIndex (C.subgroup i.succ) = 1 :=
    Subgroup.relIndex_eq_one.mpr he.symm.le
  exact (C.edgePrime i).ne_one ((C.step_index i).symm.trans hi)

/-- Normality and the proved prime index give the simple quotient at every
actual chain edge. Intermediate groups need not be normal in all of G. -/
def toWitness [Finite G] : FiniteCompositionWitness G :=
  FiniteCompositionWitness.ofPrimeIndices C.length C.subgroup C.head C.last
    C.step_lt C.step_normal (fun i => (C.step_index i).symm ▸ C.edgePrime i)

/-- Install the displayed edge orders only after their exact bindings to
the actual consecutive subgroups have been proved. -/
def toOrderCertificate [Finite G] : FiniteCompositionOrderCertificate G where
  witness := C.toWitness
  edgeOrder := C.edgeOrder
  edgeOrder_eq := C.step_index

/-- The finite arithmetic count is read directly from the displayed prime
edge orders, whose actual quotient-order bindings are proved above. -/
def ternaryCount : ℕ :=
  ∑ i : Fin C.length, if C.edgeOrder i = 3 then 1 else 0

@[simp] theorem toOrderCertificate_count [Finite G] :
    C.toOrderCertificate.count 3 = C.ternaryCount := rfl

theorem chiefWeight_le [Finite G] (c : ActualChiefSeries G) :
    actualChiefSeriesTernaryWeight c ≤ C.ternaryCount :=
  C.toOrderCertificate.chiefWeight_le c

theorem chiefWeight_le_of_count_le [Finite G] (c : ActualChiefSeries G)
    (b : ℕ) (hb : C.ternaryCount ≤ b) :
    actualChiefSeriesTernaryWeight c ≤ b := (C.chiefWeight_le c).trans hb

theorem exists_chiefSeries_le [Finite G] :
    ∃ c : ActualChiefSeries G, actualChiefSeriesTernaryWeight c ≤ C.ternaryCount :=
  C.toOrderCertificate.exists_chiefSeries_le

end SparsePrimeCompositionCertificate
end SymmetricSubgroupAsymptotics
