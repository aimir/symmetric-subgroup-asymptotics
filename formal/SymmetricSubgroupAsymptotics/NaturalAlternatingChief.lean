import SymmetricSubgroupAsymptotics.AlternatingGeneratorBridge
import Mathlib.GroupTheory.Perm.Fin

/-! Uniform bridges for the literal natural alternating generators.
The final three-cycle is written as two adjacent swaps. The first
generator is a full rotation in odd degree and the rotation with its
final adjacent swap cancelled in even degree. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

section Cycles
variable {α:Type} [Fintype α] [DecidableEq α]

theorem cycle_adjacent_commutator (σ:Equiv.Perm α) (a b c:α)
    (ha:σ a=b) (hb:σ b=c) :
    σ⁻¹*Equiv.swap b c*σ*Equiv.swap b c=Equiv.swap a b*Equiv.swap b c := by
  have hai : σ⁻¹ b=a := by
    change σ.symm b=a
    rw [←ha]
    exact σ.symm_apply_apply a
  have hbi : σ⁻¹ c=b := by
    change σ.symm c=b
    rw [←hb]
    exact σ.symm_apply_apply b
  rw [Equiv.mul_swap_eq_swap_mul (σ⁻¹) b c,hai,hbi]
  group

end Cycles

theorem cycleThreeChiefSeries_zero (n:ℕ) (hn:5≤n)
    (σ:Equiv.Perm (Fin n)) (hcycle:σ.IsCycle)
    (hsupport:σ.support=Finset.univ) (hσ:σ∈alternatingGroup (Fin n))
    (a b c:Fin n) (ha:σ a=b) (hb:σ b=c) :
    ∃z:ActualChiefSeries
      (Subgroup.closure ({σ,Equiv.swap a b*Equiv.swap b c}:
        Set (Equiv.Perm (Fin n)))),actualChiefSeriesTernaryWeight z=0 := by
  apply alternatingPairChiefSeries_zero n hn σ (Equiv.swap b c)
    (Equiv.swap a b*Equiv.swap b c) (Equiv.swap_inv b c)
  · simpa only [hb] using Equiv.Perm.closure_cycle_adjacent_swap hcycle hsupport b
  · exact hσ
  · exact hcycle.ne_one
  · exact Or.inl (cycle_adjacent_commutator σ a b c ha hb)

theorem twistedCycleThreeChiefSeries_zero (n:ℕ) (hn:5≤n)
    (σ:Equiv.Perm (Fin n)) (hcycle:σ.IsCycle)
    (hsupport:σ.support=Finset.univ)
    (a b c:Fin n) (ha:σ a=b) (hb:σ b=c) (hab:a≠b) (hac:a≠c)
    (hσ:σ*Equiv.swap b c∈alternatingGroup (Fin n)) :
    ∃z:ActualChiefSeries
      (Subgroup.closure ({σ*Equiv.swap b c,Equiv.swap a b*Equiv.swap b c}:
        Set (Equiv.Perm (Fin n)))),actualChiefSeriesTernaryWeight z=0 := by
  let s := Equiv.swap b c
  have hs : s⁻¹=s := Equiv.swap_inv b c
  have hsquare : s*s=1 := Equiv.swap_mul_self b c
  apply alternatingPairChiefSeries_zero n hn (σ*s) s
    (Equiv.swap a b*Equiv.swap b c) hs
  · apply closure_pair_top_of_mul_right
    simpa only [mul_assoc,hsquare,mul_one,hb] using
      Equiv.Perm.closure_cycle_adjacent_swap hcycle hsupport b
  · exact hσ
  · intro he
    have hsa : s a=a := by simp [s,Equiv.swap_apply_def,hab,hac]
    have heval : (σ*s) a=b := by simpa only [Equiv.Perm.mul_apply,hsa] using ha
    rw [he,Equiv.Perm.one_apply] at heval
    exact hab heval
  · right
    have hc := cycle_adjacent_commutator σ a b c ha hb
    change σ⁻¹*s*σ*s=Equiv.swap a b*Equiv.swap b c at hc
    rw [←hc]
    simp only [mul_inv_rev,inv_inv,hs,mul_assoc,hsquare,mul_one]

def naturalAlternatingFirst (k:ℕ) : Fin (k+5) := ⟨k+2,by omega⟩
def naturalAlternatingSecond (k:ℕ) : Fin (k+5) := ⟨k+3,by omega⟩
def naturalAlternatingLast (k:ℕ) : Fin (k+5) := ⟨k+4,by omega⟩

def naturalAlternatingTriple (k:ℕ) : Equiv.Perm (Fin (k+5)) :=
  Equiv.swap (naturalAlternatingFirst k) (naturalAlternatingSecond k)*
    Equiv.swap (naturalAlternatingSecond k) (naturalAlternatingLast k)

theorem naturalAlternating_rotation_first (k:ℕ) :
    finRotate (k+5) (naturalAlternatingFirst k)=naturalAlternatingSecond k := by
  apply Fin.ext
  rw [coe_finRotate_of_ne_last (show naturalAlternatingFirst k≠Fin.last (k+4) by
    intro he
    have h := congrArg Fin.val he
    dsimp [naturalAlternatingFirst] at h
    omega)]
  rfl

theorem naturalAlternating_rotation_second (k:ℕ) :
    finRotate (k+5) (naturalAlternatingSecond k)=naturalAlternatingLast k := by
  apply Fin.ext
  rw [coe_finRotate_of_ne_last (show naturalAlternatingSecond k≠Fin.last (k+4) by
    intro he
    have h := congrArg Fin.val he
    dsimp [naturalAlternatingSecond] at h
    omega)]
  rfl

/-- Odd degrees: the original full rotation and final three-cycle. -/
theorem naturalOddAlternatingChiefSeries_zero (k:ℕ) :
    ∃z:ActualChiefSeries
      (Subgroup.closure ({finRotate (2*k+5),naturalAlternatingTriple (2*k)}:
        Set (Equiv.Perm (Fin (2*k+5))))),actualChiefSeriesTernaryWeight z=0 := by
  apply cycleThreeChiefSeries_zero (2*k+5) (by omega) (finRotate (2*k+5))
    (isCycle_finRotate_of_le (by omega))
    (support_finRotate_of_le (by omega))
  · apply Equiv.Perm.mem_alternatingGroup.mpr
    rw [sign_finRotate,show 2*k+5-1=2*(k+2) by omega,pow_mul]
    norm_num
  · exact naturalAlternating_rotation_first (2*k)
  · exact naturalAlternating_rotation_second (2*k)

/-- Even degrees: the original rotation fixing the last point and final
three-cycle. The first generator is expressed by cancelling the last swap
from the full rotation. -/
theorem naturalEvenAlternatingChiefSeries_zero (k:ℕ) :
    ∃z:ActualChiefSeries
      (Subgroup.closure
        ({finRotate (2*k+1+5)*Equiv.swap (naturalAlternatingSecond (2*k+1))
          (naturalAlternatingLast (2*k+1)),naturalAlternatingTriple (2*k+1)}:
          Set (Equiv.Perm (Fin (2*k+1+5))))),actualChiefSeriesTernaryWeight z=0 := by
  apply twistedCycleThreeChiefSeries_zero (2*k+1+5) (by omega)
    (finRotate (2*k+1+5)) (isCycle_finRotate_of_le (by omega))
    (support_finRotate_of_le (by omega))
    (naturalAlternatingFirst (2*k+1)) (naturalAlternatingSecond (2*k+1))
    (naturalAlternatingLast (2*k+1))
    (naturalAlternating_rotation_first (2*k+1))
    (naturalAlternating_rotation_second (2*k+1))
  · intro he
    have h := congrArg Fin.val he
    dsimp [naturalAlternatingFirst,naturalAlternatingSecond] at h
    omega
  · intro he
    have h := congrArg Fin.val he
    dsimp [naturalAlternatingFirst,naturalAlternatingLast] at h
    omega
  · apply Equiv.Perm.mem_alternatingGroup.mpr
    have hne : naturalAlternatingSecond (2*k+1)≠naturalAlternatingLast (2*k+1) := by
      intro he
      have h := congrArg Fin.val he
      dsimp [naturalAlternatingSecond,naturalAlternatingLast] at h
      omega
    rw [map_mul,sign_finRotate,Equiv.Perm.sign_swap hne,
      show 2*k+1+5-1=2*(k+2)+1 by omega,pow_succ,pow_mul]
    norm_num

end SymmetricSubgroupAsymptotics
