import SymmetricSubgroupAsymptotics.CFSGSymplecticInitialRootLines
import SymmetricSubgroupAsymptotics.CFSGSymplecticElementaryProjectiveCenter

/-! The literal initial short-root subgroup injects into the actual
central quotient. Its field parameter is read from the original
(nonzero) off-diagonal matrix coordinate, so no faithful-root premise
or classical-group recognition is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices

def initialShortHom (K : Type) [Field K] (r : ℕ) :
    Multiplicative K →* elementaryRootGroup K (r + 1) where
  toFun a := initialShortRoot K r a.toAdd
  map_one' := initialShortRoot_zero K r
  map_mul' a b := initialShortRoot_add K r a.toAdd b.toAdd

def projectiveShortHom (K : Type) [Field K] (r : ℕ) :
    Multiplicative K →* elementaryProjective K (r + 1) :=
  (QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (r + 1)))).comp
    (initialShortHom K r)

theorem initialShort_parameter_zero_of_central (K : Type) [Field K] (r : ℕ) (hr : 0 < r)
    (a : K) (ha : initialShortRoot K r a ∈ Subgroup.center (elementaryRootGroup K (r + 1))) :
    a = 0 := by
  obtain ⟨c, hc⟩ := (elementaryRootGroup_center_iff_scalar K r (initialShortRoot K r a)).mp ha
  let j : Fin (r + 1) := ⟨1, Nat.succ_lt_succ hr⟩
  have hj : j ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    change 1 = 0 at hv
    omega
  have he := congrArg (fun M : Mat K (r + 1) => M (Sum.inl j) (Sum.inl 0)) hc
  rw [initialShortRoot_coe K r hr] at he
  simpa [initialShortMatrix, j, Matrix.one_apply, Matrix.single_apply,
    Matrix.smul_apply, smul_eq_mul, hj, Ne.symm hj] using he

theorem projectiveShortHom_injective (K : Type) [Field K] (r : ℕ) (hr : 0 < r) :
    Function.Injective (projectiveShortHom K r) := by
  apply (MonoidHom.ker_eq_bot_iff (projectiveShortHom K r)).mp
  apply bot_unique
  intro a ha
  have hc : initialShortRoot K r a.toAdd ∈
      Subgroup.center (elementaryRootGroup K (r + 1)) :=
    (QuotientGroup.eq_one_iff _).mp ha
  have hz := initialShort_parameter_zero_of_central K r hr a.toAdd hc
  exact (Subgroup.mem_bot).mpr (congrArg Multiplicative.ofAdd hz)

def projectiveShortRoot (K : Type) [Field K] (r : ℕ) :
    Subgroup (elementaryProjective K (r + 1)) := (projectiveShortHom K r).range

def projectiveShortRootEquiv (K : Type) [Field K] (r : ℕ) (hr : 0 < r) :
    Multiplicative K ≃* projectiveShortRoot K r :=
  MonoidHom.ofInjective (projectiveShortHom_injective K r hr)

theorem projectiveShortRoot_card (K : Type) [Field K] (r : ℕ) (hr : 0 < r) :
    Nat.card (projectiveShortRoot K r) = Nat.card K := by
  calc
    Nat.card (projectiveShortRoot K r) = Nat.card (Multiplicative K) :=
      Nat.card_congr (projectiveShortRootEquiv K r hr).symm.toEquiv
    _ = Nat.card K := Nat.card_congr Multiplicative.toAdd

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
