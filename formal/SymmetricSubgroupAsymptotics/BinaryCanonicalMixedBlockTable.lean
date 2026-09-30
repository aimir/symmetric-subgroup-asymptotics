import SymmetricSubgroupAsymptotics.BinaryDegreeEightSixteenPhysicalDecoration
import Mathlib.Data.Fintype.Sort

/-!
# Canonical mixed block tables from finite record families

This file supplies the generic ordering and padding step needed by concrete
source extractors.  An injective ambient-point key orders the record indices;
the resulting increasing enumeration fills the active prefix of the mixed
block table, and all remaining entries are padded by `none`.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryDegreeEightSixteenPhysicalDecoration

/-- Put a finite family of mixed block records into canonical increasing-key
order and pad it to a table of length `Cold`.

Concrete source extractors need only provide the injective least-point key
and the cardinal bound.  No arbitrary enumeration of the source family is
retained in the resulting table. -/
noncomputable def canonicalMixedBlockTableOfRecords
    {N Cold : ℕ} {I : Type*} [Fintype I]
    (key : I → Fin (2 * N))
    (hkey : Function.Injective key)
    (record : I → MixedBlockRecord N)
    (hrecord : ∀ i, (record i).leastPoint = key i)
    (hcount : Fintype.card I ≤ Cold) :
    CanonicalMixedBlockTable N Cold := by
  letI : LinearOrder I := LinearOrder.lift' key hkey
  let enum : Fin (Fintype.card I) ≃o I :=
    Fintype.orderIsoFinOfCardEq I rfl
  let table : MixedBlockTable N Cold := fun i ↦
    if hi : i.val < Fintype.card I then
      some (record (enum ⟨i.val,hi⟩))
    else
      none
  refine ⟨table,?_⟩
  refine ⟨Fintype.card I,hcount,?_,?_⟩
  · intro i
    simp [table]
  · intro i j ri rj hri hrj hij
    have hi : i.val < Fintype.card I := by
      by_contra hi
      simp [table,hi] at hri
    have hj : j.val < Fintype.card I := by
      by_contra hj
      simp [table,hj] at hrj
    have hri' : record (enum ⟨i.val,hi⟩) = ri := by
      simpa [table,hi] using hri
    have hrj' : record (enum ⟨j.val,hj⟩) = rj := by
      simpa [table,hj] using hrj
    rw [← hri',← hrj',hrecord,hrecord]
    have hindices :
        (⟨i.val,hi⟩ : Fin (Fintype.card I)) < ⟨j.val,hj⟩ :=
      hij
    have henum := enum.strictMono hindices
    exact henum

/-! ## Recovering the finite record family from the padded table -/

/-- Every source record occurs in the active prefix of the canonical padded
table.  The position is the inverse image of the source index under the
increasing enumeration used by `canonicalMixedBlockTableOfRecords`. -/
theorem canonicalMixedBlockTableOfRecords_record_occurs
    {N Cold : ℕ} {I : Type*} [Fintype I]
    (key : I → Fin (2 * N))
    (hkey : Function.Injective key)
    (record : I → MixedBlockRecord N)
    (hrecord : ∀ i, (record i).leastPoint = key i)
    (hcount : Fintype.card I ≤ Cold) (i : I) :
    ∃ j : Fin Cold,
      j.val < Fintype.card I ∧
        (canonicalMixedBlockTableOfRecords
          key hkey record hrecord hcount).1 j = some (record i) := by
  letI : LinearOrder I := LinearOrder.lift' key hkey
  let enum : Fin (Fintype.card I) ≃o I :=
    Fintype.orderIsoFinOfCardEq I rfl
  let k : Fin (Fintype.card I) := enum.symm i
  let j : Fin Cold := ⟨k.val,lt_of_lt_of_le k.isLt hcount⟩
  have hj : j.val < Fintype.card I := by
    exact k.isLt
  refine ⟨j,hj,?_⟩
  change (if hj' : j.val < Fintype.card I then
      some (record (enum ⟨j.val,hj'⟩)) else none) = some (record i)
  simp only [dif_pos hj,Option.some.injEq]
  have hindex : (⟨j.val,hj⟩ : Fin (Fintype.card I)) = k := by
    apply Fin.ext
    rfl
  rw [hindex]
  exact congrArg record (enum.apply_symm_apply i)

/-- Conversely, every occupied entry of the canonical padded table comes
from the supplied source record family.  Padding entries contribute no
spurious records. -/
theorem canonicalMixedBlockTableOfRecords_exists_of_eq_some
    {N Cold : ℕ} {I : Type*} [Fintype I]
    (key : I → Fin (2 * N))
    (hkey : Function.Injective key)
    (record : I → MixedBlockRecord N)
    (hrecord : ∀ i, (record i).leastPoint = key i)
    (hcount : Fintype.card I ≤ Cold)
    {j : Fin Cold} {r : MixedBlockRecord N}
    (hr : (canonicalMixedBlockTableOfRecords
      key hkey record hrecord hcount).1 j = some r) :
    j.val < Fintype.card I ∧ ∃ i : I, record i = r := by
  letI : LinearOrder I := LinearOrder.lift' key hkey
  let enum : Fin (Fintype.card I) ≃o I :=
    Fintype.orderIsoFinOfCardEq I rfl
  by_cases hj : j.val < Fintype.card I
  · refine ⟨hj,enum ⟨j.val,hj⟩,?_⟩
    simpa [canonicalMixedBlockTableOfRecords,hj] using hr
  · simp [canonicalMixedBlockTableOfRecords,hj] at hr

/-- Equality of two canonical padded tables matches every source record on
the left with a unique source record on the right.  The equality of records
also identifies their least-point keys; injectivity of the right-hand key
makes the matching source index unique. -/
theorem canonicalMixedBlockTableOfRecords_matching_record
    {N Cold : ℕ} {I J : Type*} [Fintype I] [Fintype J]
    (keyI : I → Fin (2 * N))
    (hkeyI : Function.Injective keyI)
    (recordI : I → MixedBlockRecord N)
    (hrecordI : ∀ i, (recordI i).leastPoint = keyI i)
    (hcountI : Fintype.card I ≤ Cold)
    (keyJ : J → Fin (2 * N))
    (hkeyJ : Function.Injective keyJ)
    (recordJ : J → MixedBlockRecord N)
    (hrecordJ : ∀ j, (recordJ j).leastPoint = keyJ j)
    (hcountJ : Fintype.card J ≤ Cold)
    (htable : canonicalMixedBlockTableOfRecords
        keyI hkeyI recordI hrecordI hcountI =
      canonicalMixedBlockTableOfRecords
        keyJ hkeyJ recordJ hrecordJ hcountJ)
    (i : I) :
    ∃! j : J, keyJ j = keyI i ∧ recordJ j = recordI i := by
  obtain ⟨k,_hkactive,hk⟩ :=
    canonicalMixedBlockTableOfRecords_record_occurs
      keyI hkeyI recordI hrecordI hcountI i
  have htables :
      (canonicalMixedBlockTableOfRecords
        keyI hkeyI recordI hrecordI hcountI).1 =
      (canonicalMixedBlockTableOfRecords
        keyJ hkeyJ recordJ hrecordJ hcountJ).1 :=
    congrArg Subtype.val htable
  have hk' :
      (canonicalMixedBlockTableOfRecords
        keyJ hkeyJ recordJ hrecordJ hcountJ).1 k = some (recordI i) := by
    rw [← htables]
    exact hk
  obtain ⟨_hkactive',j,hj⟩ :=
    canonicalMixedBlockTableOfRecords_exists_of_eq_some
      keyJ hkeyJ recordJ hrecordJ hcountJ hk'
  have hkey : keyJ j = keyI i := by
    calc
      keyJ j = (recordJ j).leastPoint := (hrecordJ j).symm
      _ = (recordI i).leastPoint := congrArg MixedBlockRecord.leastPoint hj
      _ = keyI i := hrecordI i
  refine ⟨j,⟨hkey,hj⟩,?_⟩
  intro j' hj'
  apply hkeyJ
  exact hj'.1.trans hkey.symm

end SymmetricSubgroupAsymptotics.BinaryDegreeEightSixteenPhysicalDecoration
