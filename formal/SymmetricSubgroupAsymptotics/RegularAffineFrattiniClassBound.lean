import SymmetricSubgroupAsymptotics.FrattiniAffineSmallClassBound
import SymmetricSubgroupAsymptotics.PrimitiveAffineBinarySmallClassBound

/-! Bare regular normal prime-group profiles retain their original
translation group, faithful stabilizer action and actual subgroups.
The original Frattini quotient, not an unproved elementary chart,
supplies the elementary affine image and genuine kernel factor. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.RegularAffineFrattiniClassBound

def classBudget (n : ℕ) : ℕ := if n=8 then 40 else if n=16 then 772 else
  if n=27 then 12247 else if n=32 then 351240 else 32*(2^30+1)

variable {G X : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] (P : PrimitiveAffineProfile G X)
include P

theorem binary_degree_pow_subgroup_bound (x : X) (d : ℕ) (hd3 : 3≤d) (hd6 : d≤6)
    (hdegree : Nat.card X=2^d) (H : Subgroup G) :
    Nat.card (ConjClasses H)≤FrattiniAffineSmallClassBound.binaryClassBudget d := by
  have hn : 1<Nat.card X := by
    have hh := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by omega : 1≤d)
    rw [hdegree]
    exact lt_of_lt_of_le (by decide : 1<(2:ℕ)^1) hh
  letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp hn
  letI : Fact P.p.Prime := ⟨P.p_prime⟩
  have hp := PrimitiveAffineBinarySmallClassBound.profile_prime_eq_two_of_degree_pow P x d hdegree
  let e := P.semidirectEquiv x
  let L := H.map e.symm.toMonoidHom
  let a : H ≃* L := e.symm.subgroupMap H
  letI : Finite L := Finite.of_equiv H a.toEquiv
  have hc : Nat.card (ConjClasses H)≤Nat.card (ConjClasses L) :=
    (conjugacyClass_card_congr (G:=H) (H:=L) a).le
  have hV : Nat.card P.V=P.p^d := by
    rw [hp]
    exact (P.card_eq x).trans hdegree
  exact hc.trans (FrattiniAffineSmallClassBound.binary_subgroup_class_card_le P.p P.V
    (P.complementAction x) hp P.V_pgroup (P.complementAction_injective x) d hd3 hd6 hV L)

private theorem ternary_subgroup_bound (x : X) (hdegree : Nat.card X=27)
    (H : Subgroup G) : Nat.card (ConjClasses H)≤12247 := by
  letI : Fact P.p.Prime := ⟨P.p_prime⟩
  have hpdiv : P.p∣(3:ℕ)^3 := by
    have hh := P.V_pgroup.card_eq_or_dvd
    rw [P.card_eq x,hdegree] at hh
    simpa only [show (3:ℕ)^3=27 by decide] using hh.resolve_left (by decide : (27:ℕ)≠1)
  have hp : P.p=3 := Nat.prime_eq_prime_of_dvd_pow (m:=3) P.p_prime Nat.prime_three hpdiv
  let e := P.semidirectEquiv x
  let L := H.map e.symm.toMonoidHom
  let a : H ≃* L := e.symm.subgroupMap H
  letI : Finite L := Finite.of_equiv H a.toEquiv
  have hc : Nat.card (ConjClasses H)≤Nat.card (ConjClasses L) :=
    (conjugacyClass_card_congr (G:=H) (H:=L) a).le
  have hV : Nat.card P.V=P.p^3 := by
    rw [hp]
    simpa only [show (3:ℕ)^3=27 by decide] using (P.card_eq x).trans hdegree
  exact hc.trans (FrattiniAffineSmallClassBound.ternary_subgroup_class_card_le P.p P.V
    (P.complementAction x) hp P.V_pgroup (P.complementAction_injective x) hV L)

theorem subgroup_class_card_le (x : X)
    (hdegree : Nat.card X=8 ∨ Nat.card X=16 ∨ Nat.card X=27 ∨
      Nat.card X=32 ∨ Nat.card X=64) (H : Subgroup G) :
    Nat.card (ConjClasses H)≤classBudget (Nat.card X) := by
  rcases hdegree with h8|h16|h27|h32|h64
  · have hb := binary_degree_pow_subgroup_bound P x 3 (by decide) (by decide)
      (by simpa only [show (2:ℕ)^3=8 by decide] using h8) H
    simpa [h8,classBudget,FrattiniAffineSmallClassBound.binaryClassBudget] using hb
  · have hb := binary_degree_pow_subgroup_bound P x 4 (by decide) (by decide)
      (by simpa only [show (2:ℕ)^4=16 by decide] using h16) H
    simpa [h16,classBudget,FrattiniAffineSmallClassBound.binaryClassBudget] using hb
  · simpa [h27,classBudget] using ternary_subgroup_bound P x h27 H
  · have hb := binary_degree_pow_subgroup_bound P x 5 (by decide) (by decide)
      (by simpa only [show (2:ℕ)^5=32 by decide] using h32) H
    simpa [h32,classBudget,FrattiniAffineSmallClassBound.binaryClassBudget] using hb
  · have hb := binary_degree_pow_subgroup_bound P x 6 (by decide) (by decide)
      (by simpa only [show (2:ℕ)^6=64 by decide] using h64) H
    simpa [h64,classBudget,FrattiniAffineSmallClassBound.binaryClassBudget] using hb

end SymmetricSubgroupAsymptotics.RegularAffineFrattiniClassBound
