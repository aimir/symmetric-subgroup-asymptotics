import SymmetricSubgroupAsymptotics.PuncturedAnnihilatorScalarWordIndex
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleScalarIndex
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckFixedBruhatOrderUpper
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalOuterBound
import SymmetricSubgroupAsymptotics.CFSGConjugacyMinimumIndexBound

/-! The same original middle source and scalar words have a punctured
dual orbit, so their proper-index bound improves to q^3. At field four
this gives actual index64, which pays the class-equation scaled packet
with the already proved original order and outer bounds. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoPuncturedScalarClassPacket
open CFSG.Models.Chevalley PrimitiveSocleRawStructure
open CFSGGTwoD4GeckOriginalProjection CFSGGTwoD4GeckMiddlePairingIndex
open CFSGGTwoD4GeckMiddleSourceNormalizer CFSGGTwoD4GeckMiddleScalarSourceIndex
open CFSGGTwoD4GeckMiddleScalarIndex CFSGGTwoD4GeckMiddleScalarTorus
open CFSGGTwoD4GeckMiddleCentralExtensionData
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _

private theorem source_degree_le_of_highest_motion
    (K : Type) [Field K] [Finite K] (hthree : (3 : K) ≠ 0)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    {X : Type*} [Finite X] [MulAction (sourceNormalizer K) X]
    (x : X) (hx : highestElement K • x ≠ x) : Nat.card K^3 ≤ Nat.card X := by
  calc
    Nat.card K^3 ≤ (MulAction.stabilizer (sourceNormalizer K) x).index :=
      PuncturedAnnihilatorScalarWordIndex.index_power_succ_le_of_scalar_words
        (radical K) (sourceData K hthree) p 2
        (by simp only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin])
        (scalarAction K hthree) (scalarAction_apply K hthree)
        (fun a => ⟨scalarTorus K a,scalar_words K hthree a⟩) _ hx
    _ = (MulAction.orbit (sourceNormalizer K) x).ncard := MulAction.index_stabilizer _ _
    _ ≤ Nat.card X := Set.ncard_le_card _

private theorem cube_le_proper_index
    (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective CartanMatrix.G₂ K)] (hthree : (3 : K) ≠ 0)
    (H : Subgroup (Projective CartanMatrix.G₂ K)) (hH : H ≠ ⊤) :
    Nat.card K^3 ≤ H.index := by
  letI : Finite (Projective CartanMatrix.G₂ K) :=
    Finite.of_surjective (generatedToOriginal K) (generatedToOriginal_surjective K)
  obtain ⟨x,hx⟩ := CFSGConjugateSubgroupDegree.exists_moved_coset_of_ne_one H hH
    (originalMiddle K (central K (Multiplicative.ofAdd (1 : K)))) (original_central_one_ne_one K)
  letI : MulAction (sourceNormalizer K) (Projective CartanMatrix.G₂ K ⧸ H) :=
    MulAction.compHom _ (sourceToOriginal K)
  have hm : highestElement K • x ≠ x := by
    change sourceToOriginal K (highestElement K) • x ≠ x
    rw [source_highest_eq_central]
    exact hx
  exact source_degree_le_of_highest_motion K hthree p x hm

theorem typeGTwo_field_cube_le_proper_index
    (q : CFSG.PrimePower) (hchar : q.prime ≠ 3)
    [IsSimpleGroup (CFSG.Models.G2 q)]
    (H : Subgroup (CFSG.Models.G2 q)) (hH : H ≠ ⊤) : q.order^3 ≤ H.index := by
  have hthree : (3 : q.Field) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (R := q.Field) (p := q.prime) Nat.prime_three hchar
  have hi := cube_le_proper_index q.Field q.prime hthree H hH
  rw [q.card_field] at hi
  exact hi

theorem field_four_scaled_class_cube_le_proper_index
    (q : CFSG.PrimePower) (hq : q.order=4)
    [IsSimpleGroup (CFSG.Models.G2 q)] [Finite (CFSG.Models.G2 q)]
    (hn : ¬IsMulCommutative (CFSG.Models.G2 q))
    (H : Subgroup (CFSG.Models.G2 q)) (hH : H ≠ ⊤) :
    25*(Nat.card (ConjClasses (CFSG.Models.G2 q))*
      Nat.card (Outer (CFSG.Models.G2 q)))^3 ≤ 3^H.index := by
  have hp : q.prime=2 := by
    have hd : q.prime ∣ 2^2 := by
      change q.prime ∣ 4
      rw [←hq]
      exact dvd_pow_self _ q.exponent_pos.ne'
    exact Nat.prime_eq_prime_of_dvd_pow q.prime_isPrime Nat.prime_two hd
  have hf : q.exponent=2 := Nat.pow_right_injective (by decide : 2 ≤ (2:ℕ))
    (by simpa only [CFSG.PrimePower.order,hp] using hq)
  have hchar : q.prime ≠ 3 := by omega
  have hindex : ∀ K : Subgroup (CFSG.Models.G2 q), K ≠ ⊤ → 64 ≤ K.index := by
    intro K hK
    have hi := typeGTwo_field_cube_le_proper_index q hchar K hK
    have he : q.order^3=64 := (congrArg (fun n : ℕ => n^3) hq).trans (by decide)
    exact he.symm.le.trans hi
  have hz : Subgroup.center (CFSG.Models.G2 q)=⊥ := by
    rcases (inferInstance : (Subgroup.center (CFSG.Models.G2 q)).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (hn (Subgroup.center_eq_top_iff.mp h)).elim
  have horder : Nat.card (CFSG.Models.G2 q) ≤ 48*4^14 := by
    simpa only [hq,hf] using CFSGGTwoD4GeckFixedBruhatOrderUpper.typeGTwo_order_le q hn
  have hclass : Nat.card (ConjClasses (CFSG.Models.G2 q)) ≤ 48*4^14/64+1 :=
    (CFSGConjugacyMinimumIndexBound.class_card_le_div_add_one 64 (by decide) hz hindex).trans
      (Nat.add_le_add_right (Nat.div_le_div_right horder) 1)
  have hout : Nat.card (Outer (CFSG.Models.G2 q)) ≤ 4 := by
    simpa only [hf] using CFSGGTwoD4GeckOriginalOuterBound.typeGTwo_outer_card_le_two_exponent q
  exact ((Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left (Nat.mul_le_mul hclass hout) 3)).trans
    (by decide +kernel : 25*((48*(4:ℕ)^14/64+1)*4)^3 ≤ 3^64)).trans
    (Nat.pow_le_pow_right (by decide) (hindex H hH))

end SymmetricSubgroupAsymptotics.CFSGGTwoPuncturedScalarClassPacket
