import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationSignedPermutation
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationMonomialShortAction

/-! Every literal signed-coordinate short-root unit belongs to the
actual B elementary group. The proof conjugates an original terminal
root by a genuine SL-chain signed permutation and retains its parameter. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationShortMembership
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationShortArrays
open CFSGOrthogonalBGenerationSignedPermutation CFSGOrthogonalBGenerationMonomialShortAction
variable (K : Type) [Field K]

private def coordinate {r : ℕ} (side : Bool) (i : Fin r) : Fin r ⊕ Fin r :=
  if side then Sum.inr i else Sum.inl i

private theorem terminal_short_mem (s : ℕ) (side : Bool) (a : K) :
    shortUnit K (s + 1) (coordinate side (Fin.last s)) a ∈ elementaryRootGroup K (s + 1) := by
  have hi : ¬ (Fin.last s).val + 1 < s + 1 := by simp
  cases side
  · change shortUnit K (s + 1) (Sum.inl (Fin.last s)) a ∈ _
    rw [← terminal_positive K (s + 1) (Fin.last s) hi a]
    exact rootTransvection_mem K (s + 1) false (Fin.last s) a
  · change shortUnit K (s + 1) (Sum.inr (Fin.last s)) a ∈ _
    have hh := rootTransvection_mem K (s + 1) true (Fin.last s) (-a)
    rw [terminal_negative K (s + 1) (Fin.last s) hi (-a), neg_neg] at hh
    exact hh

private theorem coordinate_short_mem (s : ℕ) (side : Bool) (i : Fin (s + 1)) (a : K) :
    shortUnit K (s + 1) (coordinate side i) a ∈ elementaryRootGroup K (s + 1) := by
  let τ : Equiv.Perm (Fin (s + 1)) := Equiv.swap i (Fin.last s)
  let σ := naturalPermutation (s + 1) τ
  let d := naturalWeight K (s + 1) i τ
  let l := CFSGOrthogonalDGenerationSignedPermutation.weight K i τ i
  let P := signedPermutationElement K (s + 1) i τ
  have hll : l * l = 1 :=
    CFSGOrthogonalDGenerationSignedPermutation.weight_mul_self K i τ i
  have hm : σ.symm (middle (s + 1)) = middle (s + 1) := by
    simp [σ, naturalPermutation, middle]
  have hb : σ.symm (Sum.inl (coordinate side (Fin.last s))) =
      Sum.inl (coordinate side i) := by
    cases side <;> simp [σ, naturalPermutation, τ, coordinate]
  have hp : σ.symm (Sum.inl (paired (s + 1) (coordinate side (Fin.last s)))) =
      Sum.inl (paired (s + 1) (coordinate side i)) := by
    cases side <;> simp [σ, naturalPermutation, τ, coordinate, paired]
  have hdm : d (middle (s + 1)) = 1 := rfl
  have hdl : d (Sum.inl (coordinate side i)) = l := by cases side <;> rfl
  have hdp : d (Sum.inl (paired (s + 1) (coordinate side i))) = l := by cases side <;> rfl
  have hc := short_conjugation P.val σ d (signedPermutationElement_val K (s + 1) i τ)
    (coordinate side (Fin.last s)) (coordinate side i) l (l * a) hm hb hp
    (by rw [hdm]; exact one_ne_zero)
    (naturalWeight_ne_zero K (s + 1) i τ _)
    (by rw [hb, hdl, hdm, mul_one])
    (by rw [hp, hdp, hdm]; exact hll.symm)
  have hh := (elementaryRootGroup K (s + 1)).mul_mem
    ((elementaryRootGroup K (s + 1)).mul_mem P.property (terminal_short_mem K s side (l * a)))
    ((elementaryRootGroup K (s + 1)).inv_mem P.property)
  rw [hc] at hh
  have ha : l * (l * a) = a := by rw [← mul_assoc, hll, one_mul]
  simpa only [ha] using hh

theorem shortUnit_mem (s : ℕ) (b : Fin (s + 1) ⊕ Fin (s + 1)) (a : K) :
    shortUnit K (s + 1) b a ∈ elementaryRootGroup K (s + 1) := by
  rcases b with (i | i)
  · exact coordinate_short_mem K s false i a
  · exact coordinate_short_mem K s true i a

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationShortMembership
