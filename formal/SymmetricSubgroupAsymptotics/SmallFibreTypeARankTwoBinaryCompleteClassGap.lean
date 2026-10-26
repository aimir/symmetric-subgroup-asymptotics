import SymmetricSubgroupAsymptotics.SmallFibreTypeARankTwoBinaryClassResidual
import SymmetricSubgroupAsymptotics.BinaryBlockUnsignedClassReserve
import SymmetricSubgroupAsymptotics.SimpleSocleQuasiprimitiveSwap
import SymmetricSubgroupAsymptotics.PrimitiveSocleBoundedComponentClassBound
import SymmetricSubgroupAsymptotics.CommutingPairIdentityReserveBound

/-! The binary seven/eight seams are paid on the SAME original correlated
kernel and actual subnormal top image. The actual simple factor has order168;
its outer bound gives top order<=336. A one-factor FULL transitive socle is
quasiprimitive, so a transposition would force the full symmetric group,
contradicting that actual order bound. No action catalogue, primitivity
assumption, split extension or full-base replacement is introduced. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SmallFibreTypeARankTwoBinaryCompleteClassGap
open PrimitiveSocleRawStructure OriginalBlockClassBound CFSGReduction

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

/-- Original binary blocks over the actual simple binary rank-two factor,
with seven or eight original blocks, satisfy the full class cube gap. -/
theorem binary_seven_eight_subnormal_class_cube_gap
    (π : Ω→X) (hπ : ∀ (g:A) (ω:Ω),π (g•ω)=g•π ω)
    (hsize : ∀x,Nat.card (originalBlockFibre π x)=2)
    (E : NonaffineData (Top (A:=A) (X:=X)) X)
    (q : CFSG.PrimePower) (hq : q.order=2)
    (e : E.Simple≃*CFSG.Models.A 2 q)
    (hk : E.factorCount=1) (hn : Nat.card X=7 ∨ Nat.card X=8)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card Ω-2) := by
  letI : Fintype X := Fintype.ofFinite X
  letI : IsSimpleGroup (CFSG.Models.A 2 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.A 2 q) := Finite.of_equiv E.Simple e.toEquiv
  have hclasses : Nat.card (ConjClasses E.Simple)=
      Nat.card (ConjClasses (CFSG.Models.A 2 q)) := by
    apply Nat.le_antisymm
    · exact Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
        (ConjClasses.map_surjective e.symm.surjective)
    · exact Nat.card_le_card_of_surjective (ConjClasses.map e.toMonoidHom)
        (ConjClasses.map_surjective e.surjective)
  have hcomponent : Nat.card (ConjClasses E.Simple)*Nat.card (Outer E.Simple)≤12 := by
    rw [hclasses,outer_card_congr e]
    exact CFSGTypeARankTwoBinaryClassPacket.component_class_card_le_twelve q hq
  have hcardS : Nat.card E.Simple=168 :=
    (Nat.card_congr e.toEquiv).trans (CFSGTypeARankTwoCardTwo.order_eq_168 q hq)
  have hf : q.exponent=1 :=
    (Nat.Prime.pow_inj' q.prime_isPrime (by decide : Nat.Prime 2)
      q.exponent_pos.ne' (by decide : (1:ℕ)≠0)
      (show q.prime^q.exponent=2^1 from hq)).2
  have houter : Nat.card (Outer E.Simple)≤2 := by
    rw [outer_card_congr e]
    simpa only [hq,hf] using
      CFSGTypeAOuterGcdCardinality.typeA_higher_outer_card_le_gcd 2 (by decide) q
  have htopCard : Nat.card (Top (A:=A) (X:=X))≤336 := by
    calc
      _≤Nat.card E.Simple*Nat.card (Outer E.Simple) := by
        simpa only [hk,pow_one,Nat.factorial_one,mul_one] using
          E.card_le_simple_outer_wreath
      _≤168*2 := Nat.mul_le_mul hcardS.le houter
      _=336 := by decide
  have hns : ∀a:A,¬(topMap (A:=A) (X:=X) a).IsSwap := by
    intro a ha
    have ht : Top (A:=A) (X:=X)=⊤ :=
      SimpleSocleQuasiprimitiveSwap.permutation_eq_top_of_single_factor_of_isSwap
        (Top (A:=A) (X:=X)) E hk (topMap (A:=A) (X:=X) a) ha ⟨a,rfl⟩
    have hsym : Nat.card (Top (A:=A) (X:=X))=(Nat.card X).factorial := by
      rw [ht,Nat.card_congr Subgroup.topEquiv.toEquiv,Nat.card_perm]
    have hlarge : 336<(Nat.card X).factorial := by
      rcases hn with hn|hn <;> rw [hn] <;> decide
    rw [hsym] at htopCard
    omega
  have htop : ∀L:Subgroup (Top (A:=A) (X:=X)),L.IsSubnormal→
      Nat.card (ConjClasses L)≤12 := by
    intro L hL
    exact (E.subnormal_class_card_le_of_factor_one hk L hL).trans hcomponent
  have hbound := BinaryBlockUnsignedClassReserve.subnormal_class_card_le_thirteen_mul
    π hπ (fun x=>(hsize x).le) (by omega) htop hns H hH
  have hnum : (13*2^(Nat.card X-2))^3≤5^(2*Nat.card X-2) := by
    rcases hn with hn|hn
    · simpa only [hn] using CommutingPairIdentityReserveBound.binary_seven
    · simpa only [hn] using CommutingPairIdentityReserveBound.binary_eight
  have hcard := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre π 2 hsize
  have hh := (Nat.pow_le_pow_left hbound 3).trans hnum
  simpa only [hcard,Nat.mul_comm (Nat.card X) 2] using hh

/-- Every original binary or ternary small-fibre action over this actual
factor is paid. All-factor and other degree forms are discharged by the
existing recurrence before the same one-factor seven/eight action is used. -/
theorem subnormal_class_cube_gap
    (π : Ω→X) (hπ : ∀ (g:A) (ω:Ω),π (g•ω)=g•π ω)
    (c : ℕ) (hc : c=2 ∨ c=3)
    (hsize : ∀x,Nat.card (originalBlockFibre π x)=c)
    (E : NonaffineData (Top (A:=A) (X:=X)) X)
    (q : CFSG.PrimePower) (hq : q.order=2)
    (e : E.Simple≃*CFSG.Models.A 2 q)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card Ω-2) := by
  rcases SmallFibreTypeARankTwoBinaryClassResidual.subnormal_gap_or_binary_seven_eight
      π hπ c hc hsize E q hq e H hH with hgap|⟨hc2,hk,K,hK,hdegree,hidx⟩
  · exact hgap
  · apply binary_seven_eight_subnormal_class_cube_gap π hπ
      (fun x=>(hsize x).trans hc2) E q hq e hk ?_ H hH
    rw [hdegree]
    exact hidx

end SymmetricSubgroupAsymptotics.SmallFibreTypeARankTwoBinaryCompleteClassGap
