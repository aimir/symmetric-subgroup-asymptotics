import SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergUniformExtension
import SymmetricSubgroupAsymptotics.CFSGHeisenbergTransitiveActionIndex

/-! The actual uniform tail action discharges the generic coupled
Heisenberg index theorem. Both factors are still obtained from the SAME
actual subgroup. No transitivity or quotient-action premise remains. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergUniformActionIndex

open CFSGHeisenbergCoordinateGroup CFSGSymplecticSerreMatrices
open CFSGSymplecticHeisenbergUniformExtension CFSGSymplecticHeisenbergVectorAction
variable (K : Type) [Field K]

local instance indexVectorActionInstance (m : ℕ) :
    MulAction (elementaryRootGroup K m) ((Fin m → K) × (Fin m → K)) := vectorAction K m

private theorem actual_transitive (m : ℕ) (hm : 2 ≤ m)
    (v w : (Fin m → K) × (Fin m → K)) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ A : elementaryRootGroup K m, A • v = w := by
  cases m with
  | zero => omega
  | succ r => exact vectorAction_nonzero_transitive K r (by omega) v w hv hw

theorem prime_mul_field_power_le_index [Finite K]
    (m : ℕ) (hm : 2 ≤ m) (hTwo : (2 : K) ≠ 0)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (M : Subgroup (Element K m ⋊[tailAction K m (by omega) hTwo] elementaryRootGroup K m))
    (hcentre : ¬(central (K := K) (m := m)).range ≤ M.comap SemidirectProduct.inl) :
    p * Nat.card K ^ (2 * m) ≤ M.index := by
  exact CFSGHeisenbergTransitiveActionIndex.prime_mul_field_power_le_index
    (tailAction K m (by omega) hTwo) p (vectorAction_zero K m)
      (actual_transitive K m hm) (coordinate_action K m (by omega) hTwo) M hcentre

theorem degree_le_of_central_motion [Finite K]
    (m : ℕ) (hm : 2 ≤ m) (hTwo : (2 : K) ≠ 0)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    {X : Type*} [Finite X]
    [MulAction (Element K m ⋊[tailAction K m (by omega) hTwo] elementaryRootGroup K m) X]
    (x : X) (c : Multiplicative K)
    (hc : (SemidirectProduct.inl (central c) :
      Element K m ⋊[tailAction K m (by omega) hTwo] elementaryRootGroup K m) • x ≠ x) :
    p * Nat.card K ^ (2 * m) ≤ Nat.card X := by
  have hmpos : 0 < m := by omega
  let M := MulAction.stabilizer
    (Element K m ⋊[tailAction K m hmpos hTwo] elementaryRootGroup K m) x
  have hcentre : ¬(central (K := K) (m := m)).range ≤ M.comap SemidirectProduct.inl := by
    intro hh
    exact hc (hh ⟨c, rfl⟩)
  calc
    p * Nat.card K ^ (2 * m) ≤ M.index := prime_mul_field_power_le_index K m hm hTwo p M hcentre
    _ = (MulAction.orbit
        (Element K m ⋊[tailAction K m hmpos hTwo] elementaryRootGroup K m) x).ncard :=
      MulAction.index_stabilizer _ _
    _ ≤ Nat.card X := Set.ncard_le_card _

end SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergUniformActionIndex
