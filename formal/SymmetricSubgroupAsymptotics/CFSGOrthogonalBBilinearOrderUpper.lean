import SymmetricSubgroupAsymptotics.MatrixUnitBilinearIsometryOrderBound
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGramNondegenerate
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalMatrixBounds
import SymmetricSubgroupAsymptotics.CFSGSymplecticSharpOrderUpper

/-! The actual odd-characteristic B representation preserves its
nondegenerate Gram form. Characteristic two uses the already proved
actual B-to-symplectic projective equivalence and sharper C order bound.
No recognition of an unrelated natural group is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBBilinearOrderUpper
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBIntrinsicLongRoots
open CFSGOrthogonalBUnipotent

theorem elementaryProjective_card_le_bilinear_power (K : Type) [Field K] [Finite K]
    (h2 : (2:K)≠0) (r : ℕ) :
    Nat.card (elementaryProjective K r) ≤ Nat.card K^(2*r^2+3*r+1) := by
  have hb := MatrixUnitBilinearIsometryOrderBound.central_quotient_card_le K (Index r)
    (elementaryRootGroup K r) (gram K r).toBilin' (gram_nondegenerate h2 r)
    (natural_pairing_invariant h2 r)
  have hI : Nat.card (Index r)=2*r+1 := by
    simp only [Nat.card_sum, Nat.card_fin, Nat.card_unique]
    omega
  have he : (2*r+1)*((2*r+1)+1)/2=2*r^2+3*r+1 := by
    symm
    apply Nat.eq_div_of_mul_eq_right (by decide : (2:ℕ)≠0)
    ring
  simpa only [hI, he] using hb

private theorem two_ne_zero (q : CFSG.PrimePower) (hq : q.prime≠2) : (2:q.Field)≠0 := by
  intro he
  have hd : q.prime ∣ 2 := (CharP.cast_eq_zero_iff q.Field q.prime 2).mp he
  exact hq ((Nat.prime_dvd_prime_iff_eq q.prime_isPrime Nat.prime_two).mp hd)

theorem typeB_order_le_bilinear_power (r : ℕ) (hr : 3≤r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.B r q)] :
    Nat.card (CFSG.Models.B r q) ≤ q.order^(2*r^2+3*r+1) := by
  obtain ⟨s,rfl⟩ : ∃s : ℕ,r=s+3 := ⟨r-3,by omega⟩
  by_cases hq : q.prime=2
  · letI : CharP q.Field 2 := by rw [←hq]; infer_instance
    let e := serreProjectiveEquivSymplecticProjective_charTwo q.Field (s+2) (by omega)
    have hquot : Nat.card (CFSGSymplecticSerreMatrices.elementaryProjective q.Field (s+3)) ≤
        Nat.card (CFSGSymplecticSerreMatrices.elementaryRootGroup q.Field (s+3)) :=
      Nat.card_le_card_of_surjective (QuotientGroup.mk' (Subgroup.center _))
        (QuotientGroup.mk'_surjective _)
    rw [Nat.card_congr e.toEquiv]
    have hb := hquot.trans
      (CFSGSymplecticSharpOrderUpper.elementary_card_le_quadratic_power q.Field (s+3))
    rw [q.card_field] at hb
    exact hb.trans (Nat.pow_le_pow_right
      (pow_pos q.prime_isPrime.pos _) (by nlinarith))
  · let e := serreProjectiveEquivElementaryProjective q.Field (s+2) (two_ne_zero q hq)
    rw [Nat.card_congr e.toEquiv]
    simpa only [q.card_field] using
      elementaryProjective_card_le_bilinear_power q.Field (two_ne_zero q hq) (s+3)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBBilinearOrderUpper
