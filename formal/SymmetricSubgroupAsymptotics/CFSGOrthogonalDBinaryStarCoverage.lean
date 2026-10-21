import SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryPairExtraction

/-! Both signs of the last-coordinate star are propagated along the
actual signed Coxeter cycle. Two adjacent recovered stars supply the
initial pair; no rank-parity exception occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryStarCoverage
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDBinaryPairElements CFSGOrthogonalDBinaryPairExtraction
open CFSGOrthogonalDBinaryArrayMembership CFSGOrthogonalDBinaryConjugation
open CFSGOrthogonalDBinaryCyclePermutation CFSGSymplecticBinaryArrayMembership
variable {K : Type} [Field K] [CharP K 2]

def StarPair (s : ℕ) (H : Subgroup ((Mat K (s + 4))ˣ)) (a : Index (s + 4)) : Prop :=
  HasArray H (rootArray (Sum.inl (lastIndex s)) a) ∧
    HasArray H (rootArray (Sum.inr (lastIndex s)) a)

theorem starPair_conjugate (s : ℕ) (H : Subgroup ((Mat K (s + 4))ˣ))
    (hW : (binarySecond K s).val ∈ H) (a : Index (s + 4)) (ha : StarPair s H a) :
    StarPair s H (cyclePerm (s + 2) a) := by
  constructor
  · have hp := hasArray_conjugate (s + 2) H hW _ _ ha.2
    change HasArray H (rootArray
      (cyclePerm (s + 2) (Sum.inr (Fin.last (s + 3)))) (cyclePerm (s + 2) a)) at hp
    rw [cyclePerm_negative_last] at hp
    exact hp
  · have hp := hasArray_conjugate (s + 2) H hW _ _ ha.1
    change HasArray H (rootArray
      (cyclePerm (s + 2) (Sum.inl (Fin.last (s + 3)))) (cyclePerm (s + 2) a)) at hp
    rw [cyclePerm_positive_last] at hp
    exact hp

def column (s : ℕ) (side : Bool) (j : Fin (s + 3)) : Index (s + 4) :=
  if side then Sum.inr j.castSucc else Sum.inl j.castSucc

theorem all_stars (s : ℕ) (H : Subgroup ((Mat K (s + 4))ˣ))
    (hx : (binaryFirst K s).val ∈ H) (hW : (binarySecond K s).val ∈ H) :
    ∀ (side : Bool) (j : Fin (s + 3)), StarPair s H (column s side j) := by
  have hstep (side : Bool) (j : ℕ) (hj : j < s + 2)
      (h : StarPair s H (column s side (⟨j, by omega⟩ : Fin (s + 3)))) :
      StarPair s H (column s side (⟨j + 1, by omega⟩ : Fin (s + 3))) := by
    have hp := starPair_conjugate s H hW _ h
    have he := cyclePerm_shift (s + 2) side j hj
    change cyclePerm (s + 2) (column s side (⟨j, by omega⟩ : Fin (s + 3))) =
      column s side (⟨j + 1, by omega⟩ : Fin (s + 3)) at he
    rw [he] at hp
    exact hp
  have hzero : StarPair s H (column s false (0 : Fin (s + 3))) :=
    ⟨first_star_mem s H hx hW, opposite_first_star_mem s H hx hW⟩
  have hp : ∀ j : ℕ, ∀ hj : j < s + 3,
      StarPair s H (column s false (⟨j, hj⟩ : Fin (s + 3))) := by
    intro j
    induction j with
    | zero => intro _; exact hzero
    | succ j ih => intro hj; exact hstep false j (by omega) (ih (by omega))
  have hnzero : StarPair s H (column s true (0 : Fin (s + 3))) := by
    have h := starPair_conjugate s H hW _ (hp (s + 2) (by omega))
    change StarPair s H (cyclePerm (s + 2) (Sum.inl (Fin.last (s + 2)).castSucc)) at h
    rw [cyclePerm_positive_penultimate] at h
    exact h
  have hn : ∀ j : ℕ, ∀ hj : j < s + 3,
      StarPair s H (column s true (⟨j, hj⟩ : Fin (s + 3))) := by
    intro j
    induction j with
    | zero => intro _; exact hnzero
    | succ j ih => intro hj; exact hstep true j (by omega) (ih (by omega))
  intro side j
  cases side
  · exact hp j.val j.isLt
  · exact hn j.val j.isLt

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryStarCoverage
