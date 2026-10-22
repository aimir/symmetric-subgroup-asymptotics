import SymmetricSubgroupAsymptotics.CFSGSerreChainInvariantSpan
import SymmetricSubgroupAsymptotics.CFSGSerreGeneratedInvariantSpan

/-! The original rational type-A quotient is spanned by its literal
Cartan generators and signed interval brackets. The proof uses only
original Serre relations and invariant linear spans. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalSource
open CFSG.Models.Chevalley CFSGSerreLocalNilpotence CFSGSerreDividedPowers
open CFSGTwistedAIntervalBrackets CFSGSerreChainInvariantSpan

def cartan (r : ℕ) (i : Fin r) : Source r :=
  generator (CartanMatrix.A r) (.H i)

def weight (r : ℕ) (neg : Bool) (i : Fin r) (j : ℕ) : ℚ :=
  if hj : j < r then
    if neg then -(CartanMatrix.A r i ⟨j, hj⟩ : ℚ)
    else (CartanMatrix.A r i ⟨j, hj⟩ : ℚ)
  else 0

theorem cartan_simple (r : ℕ) (neg : Bool) (i : Fin r) (j : ℕ) :
    ⁅cartan r i, simple r neg j⁆ = weight r neg i j • simple r neg j := by
  by_cases hj : j < r
  · simp only [simple, dif_pos hj, weight, dif_pos hj]
    cases neg
    · simpa only [cartan, rootVector, Bool.false_eq_true, if_false,
        Int.cast_smul_eq_zsmul] using generator_HE (CartanMatrix.A r) i ⟨j, hj⟩
    · simpa only [cartan, rootVector, if_true, neg_smul,
        Int.cast_smul_eq_zsmul] using generator_HF (CartanMatrix.A r) i ⟨j, hj⟩
  · simp only [simple, dif_neg hj, weight, dif_neg hj, lie_zero, smul_zero]

theorem opposite_simple_mem_cartanSpan (r : ℕ) (neg : Bool) (k j : ℕ) :
    ⁅simple r (!neg) k, simple r neg j⁆ ∈ Submodule.span ℚ (Set.range (cartan r)) := by
  let W := Submodule.span ℚ (Set.range (cartan r))
  by_cases hk : k < r
  · by_cases hj : j < r
    · simp only [simple, dif_pos hk, dif_pos hj]
      have hH : cartan r ⟨k, hk⟩ ∈ W := Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩
      by_cases he : k = j
      · subst j
        cases neg
        · change ⁅generator (CartanMatrix.A r) (.F ⟨k, hk⟩),
            generator (CartanMatrix.A r) (.E ⟨k, hk⟩)⁆ ∈ W
          rw [← lie_skew, generator_EF_same]
          exact W.neg_mem hH
        · change ⁅generator (CartanMatrix.A r) (.E ⟨k, hk⟩),
            generator (CartanMatrix.A r) (.F ⟨k, hk⟩)⁆ ∈ W
          rw [generator_EF_same]
          exact hH
      · have hne : (⟨k, hk⟩ : Fin r) ≠ ⟨j, hj⟩ := by
          intro hh; exact he (congrArg (fun i : Fin r => i.val) hh)
        cases neg
        · change ⁅generator (CartanMatrix.A r) (.F ⟨k, hk⟩),
            generator (CartanMatrix.A r) (.E ⟨j, hj⟩)⁆ ∈ W
          rw [← lie_skew, generator_EF_ne _ _ _ hne.symm, neg_zero]
          exact W.zero_mem
        · change ⁅generator (CartanMatrix.A r) (.E ⟨k, hk⟩),
            generator (CartanMatrix.A r) (.F ⟨j, hj⟩)⁆ ∈ W
          rw [generator_EF_ne _ _ _ hne]
          exact W.zero_mem
    · simp only [simple, dif_pos hk, dif_neg hj, lie_zero]
      exact W.zero_mem
  · simp only [simple, dif_neg hk, zero_lie]
    exact W.zero_mem

def oneSignSpan (r : ℕ) (neg : Bool) : Submodule ℚ (Source r) :=
  chainSpan (simple r neg) (cartan r)

def intervalSpan (r : ℕ) : Submodule ℚ (Source r) :=
  oneSignSpan r false ⊔ oneSignSpan r true

theorem oneSignSpan_le (r : ℕ) (neg : Bool) : oneSignSpan r neg ≤ intervalSpan r := by
  cases neg
  · exact le_sup_left
  · exact le_sup_right

theorem simple_mem_intervalSpan (r : ℕ) (neg : Bool) (k : ℕ) :
    simple r neg k ∈ intervalSpan r :=
  oneSignSpan_le r neg (simple_mem (simple r neg) (cartan r) k)

theorem simple_on_oneSignSpan (r : ℕ) (neg other : Bool) (k : ℕ)
    (v : Source r) (hv : v ∈ oneSignSpan r other) :
    ⁅simple r neg k, v⁆ ∈ intervalSpan r := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    rcases hv with ⟨i, rfl⟩ | ⟨⟨start, n⟩, rfl⟩
    · rw [← lie_skew, cartan_simple]
      exact (intervalSpan r).neg_mem ((intervalSpan r).smul_mem _
        (simple_mem_intervalSpan r neg k))
    · by_cases he : neg = other
      · subst neg
        exact oneSignSpan_le r other
          (simple_stable (simple r other) (cartan r) (simple_lie_far r other)
            (simple_serre_adjacent r other) (weight r other) (cartan_simple r other)
            k _ (interval_mem (simple r other) (cartan r) start n))
      · have he' : neg = !other := by cases neg <;> cases other <;> simp_all
        subst neg
        exact oneSignSpan_le r other
          (opposite_interval_mem (simple r other) (cartan r) (simple_lie_far r other)
            (simple_serre_adjacent r other) (weight r other) (cartan_simple r other)
            (simple r (!other) k) (opposite_simple_mem_cartanSpan r other k) start n)
  | zero => rw [lie_zero]; exact (intervalSpan r).zero_mem
  | add v w _ _ hv hw => rw [lie_add]; exact (intervalSpan r).add_mem hv hw
  | smul a v _ hv => rw [lie_smul]; exact (intervalSpan r).smul_mem a hv

theorem simple_preserves_intervalSpan (r : ℕ) (neg : Bool) (k : ℕ)
    (v : Source r) (hv : v ∈ intervalSpan r) :
    ⁅simple r neg k, v⁆ ∈ intervalSpan r := by
  have hle : intervalSpan r ≤ (intervalSpan r).comap
      (LieAlgebra.ad ℚ (Source r) (simple r neg k)) := by
    apply sup_le
    · intro v hv; exact simple_on_oneSignSpan r neg false k v hv
    · intro v hv; exact simple_on_oneSignSpan r neg true k v hv
  exact hle hv

theorem intervalSpan_eq_top (r : ℕ) : intervalSpan r = ⊤ := by
  apply CFSGSerreGeneratedInvariantSpan.eq_top_of_EF_stable (CartanMatrix.A r)
  · intro i
    simpa only [simple_at, rootVector, Bool.false_eq_true, if_false] using
      simple_mem_intervalSpan r false i.val
  · intro i
    simpa only [simple_at, rootVector, if_true] using
      simple_mem_intervalSpan r true i.val
  · intro i v hv
    simpa only [simple_at, rootVector, Bool.false_eq_true, if_false] using
      simple_preserves_intervalSpan r false i.val v hv
  · intro i v hv
    simpa only [simple_at, rootVector, if_true] using
      simple_preserves_intervalSpan r true i.val v hv

end SymmetricSubgroupAsymptotics.CFSGTwistedAIntervalSource
