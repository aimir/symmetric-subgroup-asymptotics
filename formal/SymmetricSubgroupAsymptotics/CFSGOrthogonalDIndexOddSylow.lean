import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexOddMiddlePower
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPartialFlagUpper
import SymmetricSubgroupAsymptotics.CFSGSylowNormalizerMaximality

/-! The literal D flag-unipotent subgroup is Sylow in odd defining
characteristic. Only p-power elements of its actual normalizer are used;
no full orthogonal order or component identification is assumed. The
characteristic-two case is deliberately excluded at the scalar step. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexOddSylow
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexUnipotent
open CFSGOrthogonalDIndexMiddlePlane CFSGOrthogonalDIndexMiddleAction
open CFSGOrthogonalDIndexOddMiddlePower CFSGOrthogonalDIndexPartialFlagUpper
variable (K : Type) [Field K]

private theorem flag_upper_diag_pow {I : Type} [Fintype I] [DecidableEq I]
    {m : ℕ} (e : I ≃ Fin m) {A : Matrix I I K} (hA : A.BlockTriangular e)
    (k : ℕ) (i : I) : (A ^ k) i i = (A i i) ^ k := by
  induction k with
  | zero => simp only [pow_zero, Matrix.one_apply_eq]
  | succ k ih =>
    rw [pow_succ, CFSGMatrixFlagSubgroups.upper_diag_mul e (hA.pow k) hA, ih, pow_succ]

theorem pPower_normalizer_mem_unipotent (s p k : ℕ) [Fact p.Prime] [CharP K p]
    (hodd : (2 : K) ≠ 0) (A : elementaryRootGroup K (s + 4))
    (hA : A ∈ Subgroup.normalizer
      (unipotent K (s + 4) : Set (elementaryRootGroup K (s + 4))))
    (hp : A ^ (p ^ k) = 1) : A ∈ unipotent K (s + 4) := by
  let a : rootNormalizer K s := ⟨A, hA⟩
  have ha : a ^ (p ^ k) = 1 := Subtype.ext hp
  have hm := middle_lower_zero_of_pPower K s p k hodd a ha
  change (A.val : Mat K (s + 4)) (Sum.inr (lastIndex s))
    (Sum.inl (lastIndex s)) = 0 at hm
  have htri := normalizer_upper_of_middle_zero K s A hA hm
  refine ⟨htri, ?_⟩
  intro i
  have hpow : (A.val : Mat K (s + 4)) ^ (p ^ k) = 1 :=
    congrArg (fun x : elementaryRootGroup K (s + 4) => (x.val : Mat K (s + 4))) hp
  have he := congrArg (fun M : Mat K (s + 4) => M i i) hpow
  dsimp only at he
  rw [flag_upper_diag_pow K (flagEquiv (s + 4)) htri, Matrix.one_apply_eq] at he
  apply iterateFrobenius_inj K p k
  simpa only [iterateFrobenius_def, one_pow] using he

theorem pSubgroup_normalizer_le_unipotent (s p : ℕ) [Fact p.Prime] [CharP K p]
    (hodd : (2 : K) ≠ 0) (P : Subgroup (elementaryRootGroup K (s + 4)))
    (hP : IsPGroup p P)
    (hPN : P ≤ Subgroup.normalizer
      (unipotent K (s + 4) : Set (elementaryRootGroup K (s + 4)))) :
    P ≤ unipotent K (s + 4) := by
  intro g hg
  obtain ⟨k, hk⟩ := hP ⟨g, hg⟩
  exact pPower_normalizer_mem_unipotent K s p k hodd g (hPN hg)
    (congrArg (fun x : P => (x : elementaryRootGroup K (s + 4))) hk)

def unipotentOddSylow [Finite K] (s p : ℕ) [Fact p.Prime] [CharP K p]
    (hodd : (2 : K) ≠ 0) : Sylow p (elementaryRootGroup K (s + 4)) :=
  CFSGSylowNormalizerMaximality.sylowOfNormalizer (unipotent K (s + 4))
    (unipotent_isPGroup K (s + 4) p)
    (pSubgroup_normalizer_le_unipotent K s p hodd)

@[simp] theorem unipotentOddSylow_coe [Finite K] (s p : ℕ) [Fact p.Prime] [CharP K p]
    (hodd : (2 : K) ≠ 0) :
    (unipotentOddSylow K s p hodd : Subgroup (elementaryRootGroup K (s + 4))) =
      unipotent K (s + 4) := rfl

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexOddSylow
