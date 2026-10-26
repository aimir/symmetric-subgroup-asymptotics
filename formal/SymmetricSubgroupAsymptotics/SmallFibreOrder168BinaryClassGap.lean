import SymmetricSubgroupAsymptotics.BinaryBlockUnsignedClassReserve
import SymmetricSubgroupAsymptotics.SimpleSocleQuasiprimitiveSwap
import SymmetricSubgroupAsymptotics.PrimitiveSocleBoundedComponentClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleSubnormalClassBound
import SymmetricSubgroupAsymptotics.GaronziMarotiLargeBlockReduction
import SymmetricSubgroupAsymptotics.CommutingPairIdentityReserveBound

/-! Shared same-source binary extension estimate for actual order168
simple factors. No small-group identification or action census occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SmallFibreOrder168BinaryClassGap
open PrimitiveSocleRawStructure OriginalBlockClassBound

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

/-- The actual order168 and outer/class packets pay binary seven/eight
actions over the same full transitive socle and actual subnormal source.
The packet is structural; concrete-model consumers must prove its inputs. -/
theorem binary_seven_eight_subnormal_class_cube_gap
    (π : Ω→X) (hπ : ∀ (g:A) (ω:Ω),π (g•ω)=g•π ω)
    (hsize : ∀x,Nat.card (originalBlockFibre π x)=2)
    (E : NonaffineData (Top (A:=A) (X:=X)) X)
    (hcardS : Nat.card E.Simple=168)
    (houter : Nat.card (Outer E.Simple)≤2)
    (hcomponent : Nat.card (ConjClasses E.Simple)*Nat.card (Outer E.Simple)≤12)
    (hk : E.factorCount=1) (hn : Nat.card X=7 ∨ Nat.card X=8)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3≤5^(Nat.card Ω-2) := by
  letI : Fintype X := Fintype.ofFinite X
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

end SymmetricSubgroupAsymptotics.SmallFibreOrder168BinaryClassGap
