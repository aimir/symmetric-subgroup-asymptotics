import SymmetricSubgroupAsymptotics.InvariantKernelQuotientRepresentatives

/-! Quotient-section stabilizer counts only require a finite family of
linear maps. No multiplication table or group instance on the row index
is needed; the original group is bound separately by reversible rows. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem linear_stabilizer_count_le_of_quotient_representatives
    {k V C : Type*} [Field k]
    [AddCommGroup V] [Module k V] [AddCommGroup C] [Module k C]
    {r : ℕ} (A : Fin r → V →ₗ[k] V)
    (W R : Submodule k V)
    (projection : V →ₗ[k] C) (sectionMap : C →ₗ[k] V)
    (hdefect : ∀ v, v - sectionMap (projection v) ∈ W)
    (hkill : ∀ i, ∀ v ∈ W, A i v - v ∈ R)
    (cap : ℕ)
    (hcount : ∀ c : C, c ≠ 0 →
      Nat.card {i : Fin r // A i (sectionMap c) - sectionMap c ∈ R} ≤ cap)
    (v : V) (hv : v ∉ W) :
    Nat.card {i : Fin r // A i v - v ∈ R} ≤ cap := by
  have hc : projection v ≠ 0 := by
    intro hz
    have hd := hdefect v
    rw [hz, map_zero, sub_zero] at hd
    exact hv hd
  have hiff (i : Fin r) : A i v - v ∈ R ↔
      A i (sectionMap (projection v)) - sectionMap (projection v) ∈ R := by
    have hd : (A i v - v) -
        (A i (sectionMap (projection v)) - sectionMap (projection v)) ∈ R := by
      have hh := hkill i _ (hdefect v)
      rw [map_sub] at hh
      convert hh using 1 <;> abel
    constructor
    · intro h
      convert R.sub_mem h hd using 1 <;> abel
    · intro h
      simpa only [sub_add_cancel] using R.add_mem hd h
  let e : {i : Fin r // A i v - v ∈ R} ≃
      {i : Fin r // A i (sectionMap (projection v)) - sectionMap (projection v) ∈ R} := {
    toFun i := ⟨i.val, (hiff i.val).mp i.property⟩
    invFun i := ⟨i.val, (hiff i.val).mpr i.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  exact (Nat.card_congr e).le.trans (hcount _ hc)

end SymmetricSubgroupAsymptotics
