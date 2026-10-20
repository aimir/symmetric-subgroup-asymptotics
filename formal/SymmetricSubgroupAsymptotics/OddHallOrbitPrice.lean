import SymmetricSubgroupAsymptotics.InducedDoubleCosetIndices
import SymmetricSubgroupAsymptotics.CyclicQuotientOddHall
import Mathlib.Algebra.Field.ZMod

/-! Literal Mackey orbits of an actual odd Hall subgroup each pay the
odd part of the original index. No orbit or Hall subgroup is substituted. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics
variable {G : Type} [Group G] [Finite G]

theorem oddHall_index (P : Subgroup G) (hP : IsTwoComplement P) :
    P.index=ordProj[2] (Nat.card G) := by
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := P))
  rw [P.index_mul_card,hP,Nat.ordProj_mul_ordCompl_eq_self]

theorem oddHall_order_cast_ne_zero (P : Subgroup G) (hP : IsTwoComplement P) :
    (Nat.card P : ZMod 2)≠0 := by
  intro hz
  have hd := (ZMod.natCast_eq_zero_iff _ _).mp hz
  rw [hP] at hd
  exact Nat.not_dvd_ordCompl Nat.prime_two (Nat.card_pos (α := G)).ne' hd

theorem inducedOrbitStabilizer_index_ambient_dvd (H P : Subgroup G) (x : G) :
    H.index∣(inducedOrbitStabilizer H P x).index*P.index := by
  let A := H.comap (MulAut.conj x).toMonoidHom
  have hle : (inducedOrbitStabilizer H P x).map P.subtype≤A := by
    rintro _ ⟨z,hz,rfl⟩
    exact hz
  have hdiv := Subgroup.index_dvd_of_le hle
  rw [Subgroup.index_map_subtype] at hdiv
  have hA : A.index=H.index :=
    H.index_comap_of_surjective (MulAut.conj x).surjective
  rwa [hA] at hdiv

theorem oddHall_localIndex_price (H P : Subgroup G) (hP : IsTwoComplement P) (x : G) :
    ordCompl[2] H.index∣(inducedOrbitStabilizer H P x).index := by
  have hdiv := (Nat.ordCompl_dvd H.index 2).trans
    (inducedOrbitStabilizer_index_ambient_dvd H P x)
  have hcop : Nat.Coprime (ordCompl[2] H.index) P.index := by
    rw [oddHall_index P hP]
    exact (Nat.coprime_ordCompl Nat.prime_two H.index_ne_zero_of_finite).symm.pow_right _
  exact hcop.dvd_of_dvd_mul_right hdiv

theorem oddHall_doubleCoset_price (H P : Subgroup G) (hP : IsTwoComplement P)
    [Fintype (DoubleCoset.Quotient (H : Set G) (P : Set G))] :
    Fintype.card (DoubleCoset.Quotient (H : Set G) (P : Set G))*ordCompl[2] H.index≤H.index := by
  calc
    _ = ∑ _q : DoubleCoset.Quotient (H : Set G) (P : Set G),ordCompl[2] H.index := by simp
    _ ≤ ∑ q : DoubleCoset.Quotient (H : Set G) (P : Set G),
        (inducedOrbitStabilizer H P q.out).index := by
      apply Finset.sum_le_sum
      intro q _
      exact Nat.le_of_dvd (Nat.pos_of_ne_zero
        (inducedOrbitStabilizer H P q.out).index_ne_zero_of_finite)
        (oddHall_localIndex_price H P hP q.out)
    _ = H.index := inducedMackey_index_sum H P

theorem oddHall_doubleCoset_count (H P : Subgroup G) (hP : IsTwoComplement P)
    [Fintype (DoubleCoset.Quotient (H : Set G) (P : Set G))] :
    Fintype.card (DoubleCoset.Quotient (H : Set G) (P : Set G))≤ordProj[2] H.index := by
  have h := oddHall_doubleCoset_price H P hP
  conv_rhs at h => rw [←Nat.ordProj_mul_ordCompl_eq_self H.index 2]
  exact (mul_le_mul_iff_left₀
    (Nat.ordCompl_pos 2 H.index_ne_zero_of_finite)).mp h

end SymmetricSubgroupAsymptotics
