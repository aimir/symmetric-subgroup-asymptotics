import SymmetricSubgroupAsymptotics.BinarySylowCoverage
import Mathlib.GroupTheory.RegularWreathProduct
import Mathlib.Algebra.BigOperators.Fin

/-! Structural Sylow roots, avoiding enumeration of all elements of S_16. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics

abbrev BinaryWreathBit := Multiplicative (ZMod 2)

def binaryWreathBitFlip : BinaryWreathBit := Multiplicative.ofAdd 1

theorem binaryWreathBit_cases (q : BinaryWreathBit) :
    q = 1 ∨ q = binaryWreathBitFlip := by revert q; decide +kernel

@[simp] theorem binaryWreathBitFlip_ne_one : binaryWreathBitFlip ≠ 1 := by decide +kernel
@[simp] theorem binaryWreathBitFlip_mul_self :
    binaryWreathBitFlip * binaryWreathBitFlip = 1 := by decide +kernel
@[simp] theorem binaryWreathBitFlip_inv : binaryWreathBitFlip⁻¹ = binaryWreathBitFlip :=
  inv_eq_of_mul_eq_one_right binaryWreathBitFlip_mul_self

/-- The copy of the old group on the first half of the original points. -/
def binaryWreathLeft (D : Type*) [Group D] : D →* D ≀ᵣ BinaryWreathBit where
  toFun d := ⟨fun q => if q = 1 then d else 1, 1⟩
  map_one' := by ext q <;> simp
  map_mul' a b := by
    ext q
    · by_cases h : q = 1 <;> simp [RegularWreathProduct.mul_left, h]
    · rfl

/-- The actual half swap. -/
def binaryWreathSwap (D : Type*) [Group D] : D ≀ᵣ BinaryWreathBit :=
  RegularWreathProduct.inl binaryWreathBitFlip

theorem binaryWreath_factorization {D : Type*} [Group D]
    (w : D ≀ᵣ BinaryWreathBit) :
    w = binaryWreathLeft D (w.left 1) *
      (binaryWreathSwap D * binaryWreathLeft D (w.left binaryWreathBitFlip) *
        (binaryWreathSwap D)⁻¹) * RegularWreathProduct.inl w.right := by
  ext q
  · rcases binaryWreathBit_cases q with rfl | rfl <;>
      simp [binaryWreathLeft, binaryWreathSwap]
  · simp [binaryWreathLeft, binaryWreathSwap]

/-- One left copy of a generating family and the half swap generate both
copies of the full wreath product. -/
theorem binaryWreath_generates {D I : Type*} [Group D]
    (gens : I → D) (hgens : Subgroup.closure (Set.range gens) = ⊤) :
    Subgroup.closure (Set.range (fun i : Option I =>
      i.elim (binaryWreathSwap D) (fun j => binaryWreathLeft D (gens j)))) = ⊤ := by
  let K := Subgroup.closure (Set.range (fun i : Option I =>
    i.elim (binaryWreathSwap D) (fun j => binaryWreathLeft D (gens j))))
  have hswap : binaryWreathSwap D ∈ K := Subgroup.subset_closure ⟨none, rfl⟩
  have hleft (d : D) : binaryWreathLeft D d ∈ K := by
    have h : Subgroup.closure (Set.range gens) ≤ K.comap (binaryWreathLeft D) := by
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨i, rfl⟩
      exact Subgroup.subset_closure ⟨some i, rfl⟩
    rw [hgens] at h
    exact h (Subgroup.mem_top d)
  apply top_unique
  intro w _
  rw [binaryWreath_factorization w]
  apply K.mul_mem (K.mul_mem (hleft _) (K.mul_mem (K.mul_mem hswap (hleft _))
    (K.inv_mem hswap)))
  rcases binaryWreathBit_cases w.right with h | h
  · rw [h, map_one]
    exact K.one_mem
  · rw [h]
    exact hswap

abbrev BinaryWreathGroup (n : ℕ) := IteratedWreathProduct BinaryWreathBit n

/-- Exactly the recursive left-copy/half-swap generators used by the finite
menu producer, before the final labelling of the points. -/
def binaryWreathGenerator : (n : ℕ) → Fin n → BinaryWreathGroup n
  | 0 => Fin.elim0
  | n + 1 => Fin.lastCases (binaryWreathSwap (BinaryWreathGroup n))
      (fun j => binaryWreathLeft (BinaryWreathGroup n) (binaryWreathGenerator n j))

theorem binaryWreathGenerator_closure (n : ℕ) :
    Subgroup.closure (Set.range (binaryWreathGenerator n)) = ⊤ := by
  induction n with
  | zero =>
    haveI : Subsingleton (BinaryWreathGroup 0) := inferInstanceAs (Subsingleton PUnit)
    exact Subsingleton.elim _ _
  | succ n ih =>
    have h := binaryWreath_generates (binaryWreathGenerator n) ih
    have hr : Set.range (binaryWreathGenerator (n+1)) =
        Set.range (fun i : Option (Fin n) => i.elim
          (binaryWreathSwap (BinaryWreathGroup n))
          (fun j => binaryWreathLeft (BinaryWreathGroup n) (binaryWreathGenerator n j))) := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        refine Fin.lastCases ?_ (fun j => ?_) i
        · exact ⟨none, by simp [binaryWreathGenerator]⟩
        · exact ⟨some j, by simp [binaryWreathGenerator]⟩
      · rintro ⟨i, rfl⟩
        cases i with
        | none => exact ⟨Fin.last n, by simp [binaryWreathGenerator]⟩
        | some j => exact ⟨j.castSucc, by simp [binaryWreathGenerator]⟩
    rw [hr]
    exact h

/-- Explicit little-endian binary labels; the last bit labels the two halves. -/
def binaryWreathPointEquiv (n : ℕ) : (Fin n → BinaryWreathBit) ≃ Fin (2^n) :=
  finFunctionFinEquiv

def binaryWreathPermHom (n : ℕ) : BinaryWreathGroup n →* Equiv.Perm (Fin (2^n)) :=
  (binaryWreathPointEquiv n).permCongrHom.toMonoidHom.comp
    (iteratedWreathToPermHom BinaryWreathBit n)

theorem binaryWreathPermHom_injective (n : ℕ) :
    Function.Injective (binaryWreathPermHom n) :=
  (binaryWreathPointEquiv n).permCongrHom.injective.comp
    (iteratedWreathToPermHomInj BinaryWreathBit n)

/-- The literal recursive generating permutations on the original labelled set. -/
def binaryWreathPermGenerator (n : ℕ) (i : Fin n) : Equiv.Perm (Fin (2^n)) :=
  binaryWreathPermHom n (binaryWreathGenerator n i)

theorem binaryWreathPermHom_range (n : ℕ) :
    (binaryWreathPermHom n).range =
      Subgroup.closure (Set.range (binaryWreathPermGenerator n)) := by
  have h := congrArg (Subgroup.map (binaryWreathPermHom n))
    (binaryWreathGenerator_closure n)
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map] at h
  simpa only [← Set.range_comp, Function.comp_def, binaryWreathPermGenerator] using h.symm

/-- The exact Sylow subgroup is constructed by the proved order of the
faithful wreath action, with no finite group-order certificate assumed. -/
def binaryWreathSylow (n : ℕ) : Sylow 2 (Equiv.Perm (Fin (2^n))) :=
  Sylow.ofCard (binaryWreathPermHom n).range (by
    rw [Nat.card_congr (MonoidHom.ofInjective (binaryWreathPermHom_injective n)).toEquiv.symm,
      IteratedWreathProduct.card]
    have hc : Nat.card BinaryWreathBit = 2 := by simp [Nat.card_eq_fintype_card]
    rw [hc, Nat.card_perm, Nat.card_fin,
      ← Nat.multiplicity_eq_factorization (by decide : Nat.Prime 2) (Nat.factorial_ne_zero _),
      Nat.Prime.multiplicity_factorial_pow (by decide : Nat.Prime 2)])

theorem binaryWreathSylow_eq_closure (n : ℕ) :
    (binaryWreathSylow n : Subgroup (Equiv.Perm (Fin (2^n)))) =
      Subgroup.closure (Set.range (binaryWreathPermGenerator n)) :=
  binaryWreathPermHom_range n

end SymmetricSubgroupAsymptotics
