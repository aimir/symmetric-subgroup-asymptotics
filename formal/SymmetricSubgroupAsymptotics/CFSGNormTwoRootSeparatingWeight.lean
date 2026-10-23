import SymmetricSubgroupAsymptotics.CFSGFiniteIntegerPositiveSeparator
import SymmetricSubgroupAsymptotics.CFSGNormTwoRootPairing
import Mathlib.Data.Fintype.Option
import Mathlib.Order.Basic

/-! An actual positive integer functional separates zero and all roots
of any finite norm-two coordinate lattice. The induced total order has
one Cartan block and one block for each literal root, with no census. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoRootSeparatingWeight
open CFSGNormTwoRootPairing CFSGFiniteIntegerPositiveSeparator
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) [Fintype (Roots A)]

def degreeSet : Finset (Fin r→ℤ) := insert 0 (Finset.univ.image (fun k : Roots A=>k.val))

abbrev WeightBlock := Option (Roots A)

def blockVector : WeightBlock A→Fin r→ℤ
  | none=>0
  | some k=>k.val

omit [Fintype (Roots A)] in
theorem root_ne_zero (k : Roots A) : k.val≠0 := by
  intro h
  have hk := k.property
  rw [h] at hk
  norm_num at hk

omit [Fintype (Roots A)] in
theorem blockVector_injective : Function.Injective (blockVector A) := by
  intro a b hab
  cases a with
  | none=>
    cases b with
    | none=>rfl
    | some k=>exact False.elim (root_ne_zero A k hab.symm)
  | some k=>
    cases b with
    | none=>exact False.elim (root_ne_zero A k hab)
    | some l=>exact congrArg some (Subtype.ext hab)

theorem blockVector_mem (a : WeightBlock A) : blockVector A a∈degreeSet A := by
  cases a with
  | none=>exact Finset.mem_insert_self _ _
  | some k=>exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩)

def separatingHeight : (Fin r→ℤ)→ₗ[ℤ]ℤ :=
  Classical.choose (exists_positive_linear_separator (degreeSet A))

theorem separatingHeight_simple_pos (i : Fin r) :
    0<separatingHeight A (Pi.single i (1:ℤ)) :=
  (Classical.choose_spec (exists_positive_linear_separator (degreeSet A))).1 i

theorem separatingHeight_injective :
    Set.InjOn (separatingHeight A) (degreeSet A : Set (Fin r→ℤ)) :=
  (Classical.choose_spec (exists_positive_linear_separator (degreeSet A))).2

def blockHeight (a : WeightBlock A) : ℤ := -separatingHeight A (blockVector A a)

theorem blockHeight_injective : Function.Injective (blockHeight A) := by
  intro a b hab
  apply blockVector_injective A
  apply separatingHeight_injective A (blockVector_mem A a) (blockVector_mem A b)
  exact neg_inj.mp hab

@[reducible] def blockOrder : LinearOrder (WeightBlock A) :=
  LinearOrder.lift' (blockHeight A) (blockHeight_injective A)

end SymmetricSubgroupAsymptotics.CFSGNormTwoRootSeparatingWeight
