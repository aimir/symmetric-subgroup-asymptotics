import SymmetricSubgroupAsymptotics.OrthogonalPointRadicalScaledClassEnvelope
import SymmetricSubgroupAsymptotics.CFSGConjugacyMinimumIndexBound
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBilinearComponentOrderCube
import SymmetricSubgroupAsymptotics.PrimitiveSocleOrthogonalBinaryRankFourClassBound

/-! The class equation improves the literal orthogonal order packet
before the small-fibre estimate is applied. The original point-radical
index is retained. Split binary rank four uses its proved class bound
and index 28; minus binary rank four remains outside the statement. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDScaledClassPacket
open PrimitiveSocleRawStructure CFSGReduction OrthogonalPointRadicalOrderCubeNumerics

private theorem center_eq_bot {S : Type} [Group S] [IsSimpleGroup S]
    (hn : ¬IsMulCommutative S) : Subgroup.center S=⊥ := by
  rcases (inferInstance : (Subgroup.center S).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (hn (Subgroup.center_eq_top_iff.mp h)).elim

private theorem scaled_of_point_index {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (r : ℕ) (hr : 4 ≤ r) (q : CFSG.PrimePower)
    (hn : ¬IsMulCommutative S) (hwindow : 3 ≤ q.order ∨ 5 ≤ r)
    (horder : Nat.card S ≤ q.order^(2*r^2+r))
    (houter : Nat.card (Outer S) ≤ q.order^6)
    (hi : ∀ K : Subgroup S, K ≠ ⊤ → minusIndex q.order r ≤ K.index)
    (K : Subgroup S) (hK : K ≠ ⊤) :
    25*(Nat.card (ConjClasses S)*Nat.card (Outer S))^3 ≤ 3^K.index := by
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow q.exponent_pos.ne' q.prime)
  have hb : 0 < minusIndex q.order r :=
    lt_of_lt_of_le (by decide : 0 < 32)
      (minusIndex_ge_thirtyTwo q.order r hq hr hwindow)
  have hclass := CFSGConjugacyMinimumIndexBound.class_card_le_div_add_one
    (minusIndex q.order r) hb (center_eq_bot hn) hi
  have hc := hclass.trans (Nat.add_le_add_right (Nat.div_le_div_right horder) 1)
  exact ((Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left (Nat.mul_le_mul hc houter) 3)).trans
    (OrthogonalPointRadicalScaledClassEnvelope.scaled_class_equation_budget
      q.order r hq hr hwindow)).trans
      (Nat.pow_le_pow_right (by decide) (hi K hK))

private theorem split_binary_four (q : CFSG.PrimePower) (hq : q.order=2)
    [IsSimpleGroup (CFSG.Models.D 4 q)] [Finite (CFSG.Models.D 4 q)]
    (K : Subgroup (CFSG.Models.D 4 q)) (hK : K ≠ ⊤) :
    25*(Nat.card (ConjClasses (CFSG.Models.D 4 q))*
      Nat.card (Outer (CFSG.Models.D 4 q)))^3 ≤ 3^K.index := by
  have hp : q.prime=2 ∧ q.exponent=1 :=
    Nat.Prime.pow_inj' q.prime_isPrime (by decide : Nat.Prime 2)
      q.exponent_pos.ne' (by decide : (1 : ℕ) ≠ 0)
      (show q.prime^q.exponent=2^1 from hq)
  letI : CharP q.Field 2 := Eq.mp (congrArg (fun p : ℕ => CharP q.Field p) hp.1)
    (inferInstance : CharP q.Field q.prime)
  let eM := CFSGOrthogonalDSerreMatrices.serreProjectiveEquivElementaryProjective q.Field 0
  letI : Finite (CFSGOrthogonalDSerreMatrices.elementaryProjective q.Field 4) :=
    Finite.of_equiv (CFSG.Models.D 4 q) eM.toEquiv
  have hc : Nat.card (ConjClasses (CFSG.Models.D 4 q)) ≤ 1536 :=
    (Nat.card_le_card_of_surjective (ConjClasses.map eM.symm.toMonoidHom)
      (ConjClasses.map_surjective eM.symm.surjective)).trans
      (CFSGOrthogonalDBinaryIsometryClassBound.projective_class_card_le q.Field
        (q.card_field.trans hq))
  have ho : Nat.card (Outer (CFSG.Models.D 4 q)) ≤ 6 := by
    simpa only [CFSGFiniteFieldAutomorphisms.primePower_card_ringAut q,hp.2,mul_one] using
      typeD_four_binary_outer_card_le q hp.1
  have hi : 28 ≤ K.index := by
    simpa only [hq] using typeD_point_radical_le_proper_index 4 (by decide) q K hK
  exact ((Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left (Nat.mul_le_mul hc ho) 3)).trans
    (by decide +kernel : 25*((1536:ℕ)*6)^3 ≤ 3^28)).trans
      (Nat.pow_le_pow_right (by decide) hi)

theorem typeD_scaled_class_cube_le_proper_index (r : ℕ) (hr : 4 ≤ r)
    (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.D r q)] [Finite (CFSG.Models.D r q)]
    (hn : ¬IsMulCommutative (CFSG.Models.D r q))
    (K : Subgroup (CFSG.Models.D r q)) (hK : K ≠ ⊤) :
    25*(Nat.card (ConjClasses (CFSG.Models.D r q))*
      Nat.card (Outer (CFSG.Models.D r q)))^3 ≤ 3^K.index := by
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow q.exponent_pos.ne' q.prime)
  by_cases hwindow : 3 ≤ q.order ∨ 5 ≤ r
  · have hf : q.exponent ≤ q.order := q.exponent.lt_two_pow_self.le.trans
      (Nat.pow_le_pow_left q.prime_isPrime.two_le q.exponent)
    have h24 : 24 ≤ q.order^5 := (by decide : 24 ≤ (2:ℕ)^5).trans
      (Nat.pow_le_pow_left hq 5)
    have ho : Nat.card (Outer (CFSG.Models.D r q)) ≤ q.order^6 :=
      (CFSGOrthogonalDProperIndexOrderBudget.typeD_outer_card_le_twentyFour_exponent r hr q).trans
        ((Nat.mul_le_mul h24 hf).trans_eq (pow_succ q.order 5).symm)
    exact scaled_of_point_index r hr q hn hwindow
      (CFSGOrthogonalBilinearOrderUpper.typeD_order_le_bilinear_power r hr q) ho
      (fun J hJ => (minusIndex_le_split q.order r hq hr).trans
        (typeD_point_radical_le_proper_index r hr q J hJ)) K hK
  · have hr4 : r=4 := by omega
    have hq2 : q.order=2 := by omega
    subst r
    exact split_binary_four q hq2 K hK

theorem typeTwistedD_scaled_class_cube_le_proper_index (r : ℕ) (hr : 4 ≤ r)
    (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TwistedD r q)]
    [Finite (CFSG.Models.TwistedD r q)]
    (hn : ¬IsMulCommutative (CFSG.Models.TwistedD r q))
    (hhead : ¬(r=4 ∧ q.order=2))
    (K : Subgroup (CFSG.Models.TwistedD r q)) (hK : K ≠ ⊤) :
    25*(Nat.card (ConjClasses (CFSG.Models.TwistedD r q))*
      Nat.card (Outer (CFSG.Models.TwistedD r q)))^3 ≤ 3^K.index := by
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow q.exponent_pos.ne' q.prime)
  have hwindow : 3 ≤ q.order ∨ 5 ≤ r := by omega
  exact scaled_of_point_index r hr q hn hwindow
    (CFSGOrthogonalBilinearOrderUpper.typeTwistedD_order_le_bilinear_power r hr q)
    ((CFSGTwistedDProperIndexOrderBudget.typeTwistedD_outer_card_le_field_fourth r hr q hn).trans
      (Nat.pow_le_pow_right (by omega : 0 < q.order) (by decide : 4 ≤ 6)))
    (typeTwistedD_point_radical_le_proper_index r hr q) K hK

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDScaledClassPacket
