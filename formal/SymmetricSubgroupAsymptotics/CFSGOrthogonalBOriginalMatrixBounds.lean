import SymmetricSubgroupAsymptotics.CFSGOrthogonalBIndexStar
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBCharTwoProjectiveEquiv
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOuterCardinality
import SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalOrderUpper
import SymmetricSubgroupAsymptotics.CFSGSymplecticIndexStarLower
import SymmetricSubgroupAsymptotics.CFSGSymplecticOuterCardinality
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldAutomorphismsParameters
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! Uniform ORIGINAL B model bounds through its actual two natural
realizations. Characteristic two lands in the literal C elementary
quotient, whose simplicity is transported from B; simplicity of an
independent original C model is never assumed. Odd characteristic uses
the proved original B projective equivalence. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalMatrixBounds
open CFSGOrthogonalBSerreMatrices CFSGReduction PrimitiveSocleRawStructure

private theorem two_ne_zero (q : CFSG.PrimePower) (hq : q.prime≠2) : (2 : q.Field)≠0 := by
  intro he
  have hd : q.prime∣2 := (CharP.cast_eq_zero_iff q.Field q.prime 2).mp he
  exact hq ((Nat.prime_dvd_prime_iff_eq q.prime_isPrime Nat.prime_two).mp hd)

private theorem map_ne_top {A B : Type} [Group A] [Group B]
    (e : A≃*B) (H : Subgroup A) (hH : H≠⊤) : H.map e.toMonoidHom≠⊤ := by
  intro ht
  apply hH
  apply Subgroup.map_injective (f:=e.toMonoidHom) e.injective
  exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm

theorem typeB_field_power_le_proper_index (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.B r q)]
    (H : Subgroup (CFSG.Models.B r q)) (hH : H≠⊤) : q.order^(r-1) ≤ H.index := by
  obtain ⟨s,rfl⟩ : ∃ s : ℕ, r=s+3 := ⟨r-3,by omega⟩
  by_cases hq : q.prime=2
  · letI : CharP q.Field 2 := by rw [←hq]; infer_instance
    let e := serreProjectiveEquivSymplecticProjective_charTwo q.Field (s+2) (by omega)
    letI : IsSimpleGroup (CFSGSymplecticSerreMatrices.elementaryProjective q.Field (s+3)) :=
      e.symm.isSimpleGroup
    have hi := CFSGSymplecticIndexStarLower.projective_field_power_le_proper_index
      q.Field (s+3) (by omega) (H.map e.toMonoidHom) (map_ne_top e H hH)
    have hidx : (H.map e.toMonoidHom).index=H.index := H.index_map_equiv e
    simpa only [q.card_field,hidx] using hi
  · let e := serreProjectiveEquivElementaryProjective q.Field (s+2) (two_ne_zero q hq)
    letI : IsSimpleGroup (elementaryProjective q.Field (s+3)) := e.symm.isSimpleGroup
    have hi := CFSGOrthogonalBIndexStar.projective_field_power_le_proper_index q.Field s
      (H.map e.toMonoidHom) (map_ne_top e H hH)
    have hidx : (H.map e.toMonoidHom).index=H.index := H.index_map_equiv e
    simpa only [q.card_field,hidx,show s+3-1=s+2 by omega] using hi

theorem typeB_order_le_matrix_power (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.B r q)] :
    Nat.card (CFSG.Models.B r q) ≤ q.order^((2*r+1)^2) := by
  obtain ⟨s,rfl⟩ : ∃ s : ℕ, r=s+3 := ⟨r-3,by omega⟩
  by_cases hq : q.prime=2
  · letI : CharP q.Field 2 := by rw [←hq]; infer_instance
    let e := serreProjectiveEquivSymplecticProjective_charTwo q.Field (s+2) (by omega)
    have hc := MatrixUnitSubgroupOrderUpper.central_quotient_card_le_matrix_space q.Field
      (CFSGSymplecticSerreMatrices.Index (s+3))
      (CFSGSymplecticSerreMatrices.elementaryRootGroup q.Field (s+3))
    have hI : Nat.card (CFSGSymplecticSerreMatrices.Index (s+3))=2*(s+3) := by
      simp only [CFSGSymplecticSerreMatrices.Index,Nat.card_sum,Nat.card_fin,two_mul]
    have hs : Nat.card (CFSG.Models.B (s+3) q) ≤ q.order^(4*(s+3)^2) := by
      rw [Nat.card_congr e.toEquiv]
      simpa only [hI,q.card_field,show 2*(s+3)*(2*(s+3))=4*(s+3)^2 by ring] using hc
    have hqpos : 0<q.order := pow_pos q.prime_isPrime.pos _
    exact hs.trans (Nat.pow_le_pow_right hqpos (by nlinarith))
  · let e := serreProjectiveEquivElementaryProjective q.Field (s+2) (two_ne_zero q hq)
    rw [Nat.card_congr e.toEquiv]
    have hc := MatrixUnitSubgroupOrderUpper.central_quotient_card_le_matrix_space q.Field
      (Index (s+3)) (elementaryRootGroup q.Field (s+3))
    have hI : Nat.card (Index (s+3))=2*(s+3)+1 := by
      simp only [Index,Nat.card_sum,Nat.card_fin,Nat.card_unique]
      omega
    simpa only [hI,q.card_field,pow_two] using hc

theorem typeB_outer_card_le_three_exponent (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.B r q)] :
    Nat.card (Outer (CFSG.Models.B r q)) ≤ 3*q.exponent := by
  obtain ⟨s,rfl⟩ : ∃ s : ℕ, r=s+3 := ⟨r-3,by omega⟩
  by_cases hq : q.prime=2
  · letI : CharP q.Field 2 := by rw [←hq]; infer_instance
    let e := serreProjectiveEquivSymplecticProjective_charTwo q.Field (s+2) (by omega)
    letI : IsSimpleGroup (CFSGSymplecticSerreMatrices.elementaryProjective q.Field (s+3)) :=
      e.symm.isSimpleGroup
    rw [CFSGReduction.outer_card_congr e]
    simpa only [Nat.add_assoc,Nat.reduceAdd,CFSGFiniteFieldAutomorphisms.primePower_card_ringAut q]
      using CFSGSymplecticPointRootLabels.binary_outer_card_le (K:=q.Field) (s+2) (by omega)
  · have ho := (typeB_odd_outer_card_le (s+3) (by omega) q (two_ne_zero q hq)).trans
      (Nat.mul_le_mul_right (Nat.card (q.Field≃+*q.Field)) (by decide : 2≤3))
    simpa only [CFSGFiniteFieldAutomorphisms.primePower_card_ringAut q] using ho

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalMatrixBounds
