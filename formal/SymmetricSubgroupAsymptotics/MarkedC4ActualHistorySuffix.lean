import SymmetricSubgroupAsymptotics.MarkedC4ActualRawProjectionHistory

/-! The suffix of a raw marked peel has EXACTLY the remaining original
normal-chain entries. This is the closure needed to recurse inside one
fixed history menu instead of summing a new menu at each depth. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualHistorySuffix
open ActualPeelNormalChains

variable {t : ℕ} (F : Fin (t+1) → Type) [∀ i,Group (F i)]
  (M : Type) [Group M] (J : Subgroup ((∀ i,F i) × M))
abbrev Tail := fun j : Fin t => F j.succ

def tailMap : ((∀ i,F i) × M) →* ((∀ j,Tail F j) × M) where
  toFun z := ((fun j => z.1 j.succ),z.2)
  map_one' := rfl
  map_mul' _ _ := rfl

def source : Subgroup ((∀ j,Tail F j) × M) := J.map (tailMap F M)

private theorem mem_remaining_one {n : ℕ} (i : Fin n) (m : ℕ) :
    i∈remaining (1 : Equiv.Perm (Fin n)) m ↔ m ≤ i.val := by
  change i∈Finset.univ.filter (fun j : Fin n => m ≤ j.val) ↔ m ≤ i.val
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]

/-- Exact identity of actual ORIGINAL-factor intersections after the
first physical factor is forgotten; marker zero is retained on both sides. -/
theorem factor_suffix (m : ℕ) (j : Fin t) :
    factor (Tail F) (source F M J) (remaining 1 m) j=
      factor F J (remaining 1 (m+1)) j.succ := by
  ext g
  constructor
  · rintro ⟨e,he,heg⟩
    obtain ⟨z,hz,hze⟩ := e.property
    let h : J := ⟨z,hz⟩
    refine ⟨h,⟨?_,?_⟩,?_⟩
    · change z.2=1
      exact (congrArg (fun w : (∀ k,Tail F k) × M => w.2) hze).trans he.1
    · apply Subgroup.mem_iInf.mpr
      intro k
      have hkm : m+1≤k.val.val := (mem_remaining_one k.val (m+1)).mp k.property.1
      have hkne : k.val≠j.succ := k.property.2
      obtain ⟨l,hl⟩ := Fin.exists_succ_eq_of_ne_zero (show k.val≠0 by
        intro hk
        rw [hk] at hkm
        simp only [Fin.val_zero] at hkm
        omega)
      have hlm : m≤l.val := by rw [← hl] at hkm; simp only [Fin.val_succ] at hkm; omega
      have hlne : l≠j := by intro heq; apply hkne; rw [← hl,heq]
      have hel := (Subgroup.mem_iInf.mp he.2)
        ⟨l,(mem_remaining_one l m).mpr hlm,hlne⟩
      have hcoord := congrArg (fun w : (∀ k,Tail F k) × M => w.1 l) hze
      change z.1 k.val=1
      rw [← hl]
      exact hcoord.trans hel
    · have hcoord := congrArg (fun w : (∀ k,Tail F k) × M => w.1 j) hze
      exact hcoord.trans heg
  · rintro ⟨h,hh,hhg⟩
    let e : source F M J := ⟨tailMap F M h.val,⟨h.val,h.property,rfl⟩⟩
    refine ⟨e,⟨?_,?_⟩,hhg⟩
    · exact hh.1
    · apply Subgroup.mem_iInf.mpr
      intro k
      have hkm : m≤k.val.val := (mem_remaining_one k.val m).mp k.property.1
      have hmem : k.val.succ∈remaining (1 : Equiv.Perm (Fin (t+1))) (m+1) :=
        (mem_remaining_one k.val.succ (m+1)).mpr (by
          change m+1 ≤ k.val.val+1
          omega)
      have hne : k.val.succ≠j.succ := fun heq => k.property.2 (Fin.succ_injective _ heq)
      exact (Subgroup.mem_iInf.mp hh.2) ⟨k.val.succ,hmem,hne⟩

end SymmetricSubgroupAsymptotics.MarkedC4.ActualHistorySuffix
