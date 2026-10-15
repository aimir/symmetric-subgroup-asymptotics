import SymmetricSubgroupAsymptotics.FiniteConjugacyCentralizerCard
import SymmetricSubgroupAsymptotics.FiniteConjugacyCentralizerCardinalCover
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Exact conjugacy certificates from centralizer upper bounds

Separated selected conjugacy classes have total cardinality at most the group
order. If upper bounds on their centralizers already give a class-size sum
of the whole group order, every class-size inequality is an equality.
The orbit--stabilizer product then makes the centralizer bounds themselves
exact; no divisibility premise on the proposed bounds is needed.

This permits a structural kernel/image upper bound in place of listing every
commuting element. Separation and the numerical exhaustion are still explicit
proof obligations; no completeness claim about a selected list is assumed.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace FiniteConjugacyCentralizerUpperBounds

variable {G : Type*} [Group G] [Finite G] {c : ℕ}

/-- Pairwise disjoint conjugacy classes cannot exceed the group order. -/
theorem class_card_sum_le (representative : Fin c → G)
    (separated : ∀ i j, IsConj (representative i) (representative j) → i = j) :
    (∑ i : Fin c, Nat.card {x : G // IsConj x (representative i)}) ≤ Nat.card G := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI (i : Fin c) : Fintype {x : G // IsConj x (representative i)} :=
    Fintype.ofFinite _
  let f : (Σ i : Fin c, {x : G // IsConj x (representative i)}) → G :=
    fun x => x.2.1
  have hf : Function.Injective f := by
    rintro ⟨i, x⟩ ⟨j, y⟩ hxy
    have hval : (x : G) = (y : G) := hxy
    have hy : IsConj (x : G) (representative j) := by
      rw [hval]
      exact y.property
    have hij : i = j := separated i j (x.property.symm.trans hy)
    subst j
    have hsub : x = y := Subtype.ext hval
    subst y
    rfl
  have h := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_eq_fintype_card, Fintype.card_sigma] using h

/-- Saturation of the class-size lower bounds makes each one exact. -/
theorem class_card_eq (representative : Fin c → G)
    (separated : ∀ i j, IsConj (representative i) (representative j) → i = j)
    (bound : Fin c → ℕ)
    (centralizer_le : ∀ i,
      Nat.card (Subgroup.centralizer ({representative i} : Set G)) ≤ bound i)
    (class_sum : (∑ i : Fin c, Nat.card G / bound i) = Nat.card G)
    (i : Fin c) :
    Nat.card {x : G // IsConj x (representative i)} = Nat.card G / bound i := by
  have hle : ∀ j : Fin c, Nat.card G / bound j ≤
      Nat.card {x : G // IsConj x (representative j)} := by
    intro j
    rw [isConj_card_eq_div_centralizer]
    exact Nat.div_le_div_left (centralizer_le j) Nat.card_pos
  have hsum : (∑ j : Fin c, Nat.card G / bound j) =
      ∑ j : Fin c, Nat.card {x : G // IsConj x (representative j)} := by
    apply le_antisymm
    · exact Finset.sum_le_sum fun j _ => hle j
    · rw [class_sum]
      exact class_card_sum_le representative separated
  exact ((Finset.sum_eq_sum_iff_of_le (fun j _ => hle j)).mp
    hsum i (Finset.mem_univ i)).symm

/-- An exact class-size quotient recovers the exact centralizer bound. -/
theorem centralizer_card_eq (representative : Fin c → G)
    (separated : ∀ i j, IsConj (representative i) (representative j) → i = j)
    (bound : Fin c → ℕ)
    (centralizer_le : ∀ i,
      Nat.card (Subgroup.centralizer ({representative i} : Set G)) ≤ bound i)
    (class_sum : (∑ i : Fin c, Nat.card G / bound i) = Nat.card G)
    (i : Fin c) :
    Nat.card (Subgroup.centralizer ({representative i} : Set G)) = bound i := by
  let C : Subgroup G := Subgroup.centralizer ({representative i} : Set G)
  have hactual : Nat.card C ∣ Nat.card G := ⟨C.index, C.card_mul_index.symm⟩
  have hclass := class_card_eq representative separated bound centralizer_le class_sum i
  letI : Nonempty {x : G // IsConj x (representative i)} :=
    ⟨⟨representative i, IsConj.refl _⟩⟩
  have hmul_actual :
      Nat.card {x : G // IsConj x (representative i)} * Nat.card C = Nat.card G := by
    rw [isConj_card_eq_div_centralizer]
    exact Nat.div_mul_cancel hactual
  have hmul_bound :
      Nat.card {x : G // IsConj x (representative i)} * bound i ≤ Nat.card G := by
    rw [hclass]
    exact Nat.div_mul_le_self _ _
  apply le_antisymm (centralizer_le i)
  exact Nat.le_of_mul_le_mul_left (hmul_bound.trans_eq hmul_actual.symm) Nat.card_pos

/-- Preserve the existing exact-centralizer certificate interface while
supplying only proved upper bounds and the numerical exhaustion. -/
def toCardinalCover (representative : Fin c → G)
    (separated : ∀ i j, IsConj (representative i) (representative j) → i = j)
    (bound : Fin c → ℕ)
    (centralizer_le : ∀ i,
      Nat.card (Subgroup.centralizer ({representative i} : Set G)) ≤ bound i)
    (class_sum : (∑ i : Fin c, Nat.card G / bound i) = Nat.card G) :
    FiniteConjugacyCentralizerCardinalCover representative where
  separated := separated
  centralizerCard := bound
  centralizer_card := centralizer_card_eq representative separated bound
    centralizer_le class_sum
  class_card_sum := class_sum

variable {H : Type*} [Group H]

omit [Finite G] in
/-- In particular, centralizer restrictions may be bounded through their
actual kernel and range, without replacing the range by a presumed quotient. -/
theorem card_le_of_kernel_range (f : G →* H) {k t : ℕ}
    (hkernel : Nat.card f.ker ≤ k) (hrange : Nat.card f.range ≤ t) :
    Nat.card G ≤ k * t := by
  calc
    Nat.card G = Nat.card f.ker * Nat.card f.range := by
      simpa only [Subgroup.index_ker] using f.ker.card_mul_index.symm
    _ ≤ k * t := Nat.mul_le_mul hkernel hrange

omit [Finite G] in
/-- Injective coordinate codes suffice; neither code needs a surjectivity
proof or a list of all kernel/image elements. -/
theorem card_le_of_kernel_range_codes (f : G →* H) {k t : ℕ}
    (kernelCode : f.ker → Fin k) (kernelCode_injective : Function.Injective kernelCode)
    (rangeCode : f.range → Fin t) (rangeCode_injective : Function.Injective rangeCode) :
    Nat.card G ≤ k * t := by
  apply card_le_of_kernel_range f
  · simpa only [Nat.card_fin] using
      Nat.card_le_card_of_injective kernelCode kernelCode_injective
  · simpa only [Nat.card_fin] using
      Nat.card_le_card_of_injective rangeCode rangeCode_injective

end FiniteConjugacyCentralizerUpperBounds
end SymmetricSubgroupAsymptotics

end
