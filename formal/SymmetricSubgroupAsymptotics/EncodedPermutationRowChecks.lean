import SymmetricSubgroupAsymptotics.FiniteCayleyGroup
import SymmetricSubgroupAsymptotics.FinitePermutationCodeGroup
import SymmetricSubgroupAsymptotics.FiniteConjugacyGeneratorInvariant
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Data.Fintype.Card

/-!
# Permutation-code checks for faithful finite row groups

The faithful row-group operations are defined by walks along parent words.
Their correctness need not be recomputed by finite decision procedures.
These lemmas transfer commutation and generator conjugation directly to
the literal permutation codes, using faithfulness once in the generic proof.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

namespace EncodedCayleyCertificate

variable {ι : Type*} {d n : ℕ} {generators : ι → Equiv.Perm (Fin d)}
    (C : EncodedCayleyCertificate (permutationGeneratorEncoding generators) n)
    (hinj : Function.Injective C.rows)
    (prev : Fin n → ι → Fin n) (hprev : ∀ i j, C.next (prev i j) j = i)

/-- The faithful row homomorphism has the stored code, without evaluating
its defining parent word. -/
theorem rowHom_permutationCode (x : FiniteGroupRow n) :
    permutationCode (C.rowHom hinj prev hprev x) = C.rows x.index :=
  C.encode_elements x.index

/-- Commutation can be decided using only two compositions of stored codes. -/
theorem row_commute_iff_permutationCodeMul (x y : FiniteGroupRow n) :
    letI := C.rowGroup hinj prev hprev
    x * y = y * x ↔
      permutationCodeMul (C.rows x.index) (C.rows y.index) =
        permutationCodeMul (C.rows y.index) (C.rows x.index) := by
  letI := C.rowGroup hinj prev hprev
  constructor
  · intro h
    have hc := congrArg (fun z ↦ permutationCode (C.rowHom hinj prev hprev z)) h
    simpa only [map_mul, permutationCode_mul, C.rowHom_permutationCode] using hc
  · intro h
    apply C.rowHom_injective hinj prev hprev
    apply permutationCode_injective d
    simpa only [map_mul, permutationCode_mul, C.rowHom_permutationCode] using h

/-- The centralizer predicate reduces to arithmetic on the literal codes. -/
theorem row_mem_centralizer_iff_permutationCodeMul (x y : FiniteGroupRow n) :
    letI := C.rowGroup hinj prev hprev
    x ∈ Subgroup.centralizer ({y} : Set (FiniteGroupRow n)) ↔
      permutationCodeMul (C.rows x.index) (C.rows y.index) =
        permutationCodeMul (C.rows y.index) (C.rows x.index) := by
  letI := C.rowGroup hinj prev hprev
  exact Subgroup.mem_centralizer_singleton_iff.trans
    (C.row_commute_iff_permutationCodeMul hinj prev hprev x y)

/-- Count a centralizer directly on the original row indices. The finite
predicate contains no row multiplication, inverse, or parent-word walk. -/
theorem row_centralizer_card_permutationCodeMul (j : Fin n) :
    letI := C.rowGroup hinj prev hprev
    Nat.card (Subgroup.centralizer
      ({(⟨j⟩ : FiniteGroupRow n)} : Set (FiniteGroupRow n))) =
      (Finset.univ.filter (fun i : Fin n ↦
        permutationCodeMul (C.rows i) (C.rows j) =
          permutationCodeMul (C.rows j) (C.rows i))).card := by
  letI := C.rowGroup hinj prev hprev
  let e : Subgroup.centralizer
      ({(⟨j⟩ : FiniteGroupRow n)} : Set (FiniteGroupRow n)) ≃
      {i : Fin n // permutationCodeMul (C.rows i) (C.rows j) =
        permutationCodeMul (C.rows j) (C.rows i)} :=
    { toFun := fun x ↦ ⟨x.1.index,
        (C.row_mem_centralizer_iff_permutationCodeMul hinj prev hprev x.1 ⟨j⟩).mp x.2⟩
      invFun := fun i ↦ ⟨⟨i.1⟩,
        (C.row_mem_centralizer_iff_permutationCodeMul hinj prev hprev ⟨i.1⟩ ⟨j⟩).mpr i.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- A checked left inverse of the literal code table recovers any row from
the code of its faithful image. -/
theorem row_index_eq_decode_permutationCode
    (decode : Fin (d ^ d) → Fin n) (hdecode : Function.LeftInverse decode C.rows)
    (x : FiniteGroupRow n) :
    x.index = decode (permutationCode (C.rowHom hinj prev hprev x)) := by
  rw [C.rowHom_permutationCode]
  exact (hdecode x.index).symm

/-- Generator conjugation is two code compositions followed by the checked
code lookup. Only the literal original generator and its inverse occur. -/
theorem row_generator_conjugate_index
    (decode : Fin (d ^ d) → Fin n) (hdecode : Function.LeftInverse decode C.rows)
    (j : ι) (x : FiniteGroupRow n) :
    letI := C.rowGroup hinj prev hprev
    (((⟨C.next C.identity j⟩ : FiniteGroupRow n) * x *
      (⟨C.next C.identity j⟩ : FiniteGroupRow n)⁻¹)).index =
      decode (permutationCodeMul
        (permutationCodeMul (permutationCode (generators j)) (C.rows x.index))
        (permutationCode ((generators j)⁻¹))) := by
  letI := C.rowGroup hinj prev hprev
  have hg : C.rowHom hinj prev hprev ⟨C.next C.identity j⟩ = generators j := by
    change C.toCayley.elements (C.toCayley.next C.toCayley.identity j) = _
    rw [C.toCayley.next_eq, C.toCayley.identity_eq, one_mul]
  rw [C.row_index_eq_decode_permutationCode hinj prev hprev decode hdecode]
  simp only [map_mul, map_inv, hg, permutationCode_mul, C.rowHom_permutationCode]

/-- A check on stored permutation codes supplies the generator-invariance
field used by the conjugacy-class separation certificate. -/
theorem row_generator_invariant_of_permutationCodes
    {Label : Type*} (label : Fin n → Label)
    (decode : Fin (d ^ d) → Fin n) (hdecode : Function.LeftInverse decode C.rows)
    (checked : ∀ (j : ι) (i : Fin n),
      label (decode (permutationCodeMul
        (permutationCodeMul (permutationCode (generators j)) (C.rows i))
        (permutationCode ((generators j)⁻¹)))) = label i) :
    letI := C.rowGroup hinj prev hprev
    ∀ (j : ι) (x : FiniteGroupRow n),
      label (((⟨C.next C.identity j⟩ : FiniteGroupRow n) * x *
        (⟨C.next C.identity j⟩ : FiniteGroupRow n)⁻¹)).index = label x.index := by
  letI := C.rowGroup hinj prev hprev
  intro j x
  rw [C.row_generator_conjugate_index hinj prev hprev decode hdecode]
  exact checked j x.index

end EncodedCayleyCertificate
end SymmetricSubgroupAsymptotics

end
