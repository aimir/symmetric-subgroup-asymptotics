import SymmetricSubgroupAsymptotics.PrimitiveRelativeHeadOrderBudgets
import SymmetricSubgroupAsymptotics.PrimitiveAffineComplementRepresentationCore
import SymmetricSubgroupAsymptotics.PrimitiveAffineMediumOddSource
import Mathlib.Data.Nat.Factorization.PrimePow

/-! The actual affine translation subgroup supplies the generic primitive
head-order debt. Prime-degree affine order estimates remain on the original
action and do not require a finite affine locator. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineProfile

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X]
    (P : PrimitiveAffineProfile G X) (hp : MulAction.IsPreprimitive G X)

include P hp in
theorem subtypeSelfCentralizing :
    ∀ c : G,(∀ v : P.V,c*(v : G)=(v : G)*c) → c∈P.V := by
  intro c hc
  exact P.selfCentralizing hp c (fun v hv => hc ⟨v,hv⟩)

include P hp in
/-- Actual affine degrees are prime powers, including the actual positive
translation dimension. -/
theorem degree_isPrimePow : IsPrimePow (Nat.card X) := by
  let C := P.elementaryChart hp
  letI : Fact P.p.Prime := C.primeFact
  letI : AddCommGroup C.V := C.addCommGroup
  letI : Module (ZMod P.p) C.V := C.module
  letI : FiniteDimensional (ZMod P.p) C.V := C.finiteDimensional
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v)) C.equiv.symm.injective
  let x : X := Classical.choice inferInstance
  apply (isPrimePow_nat_iff (Nat.card X)).mpr
  exact ⟨P.p,C.d,P.p_prime,C.d_pos,(P.degree_eq_prime_pow_finrank C.equiv x).symm⟩

include P hp in
theorem relativeHead_add_degreeFactorization_budget
    (q : ℕ) [Fact q.Prime] (hq : Nat.card X≠q)
    (N : Subgroup G) [N.Normal] :
    Module.finrank (ZMod q) (primeRelativeCharacters q N)+(Nat.card X).factorization q≤
      (Nat.card G).factorization q := by
  letI : MulAction.IsPreprimitive G X := hp
  letI : MulAction.IsPretransitive P.V X := ⟨fun x y => by
    obtain ⟨v,hv,_⟩ := P.regular x y
    exact ⟨v,hv⟩⟩
  exact primeRelativeHead_add_degreeFactorization_le_groupFactorization q P.V
    (P.minimal hp) (P.subtypeSelfCentralizing hp) hq N

include P hp in
theorem card_le_degree_sq_of_degree_prime (hdegree : (Nat.card X).Prime) :
    Nat.card G≤Nat.card X^2 := by
  let C := P.elementaryChart hp
  letI : Fact P.p.Prime := C.primeFact
  letI : AddCommGroup C.V := C.addCommGroup
  letI : Module (ZMod P.p) C.V := C.module
  letI : FiniteDimensional (ZMod P.p) C.V := C.finiteDimensional
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v)) C.equiv.symm.injective
  let x : X := Classical.choice inferInstance
  have hpower : P.p^C.d=Nat.card X^1 := by
    simpa only [pow_one] using (P.degree_eq_prime_pow_finrank C.equiv x).symm
  have hd : C.d=1 :=
    (prime_pow_positive_injective P.p_prime hdegree C.d_pos (by decide) hpower).2
  have hb := P.card_le_degree_pow_finrank_succ C.equiv x
  change Nat.card G≤Nat.card X^(C.d+1) at hb
  simpa only [hd] using hb

end SymmetricSubgroupAsymptotics.PrimitiveAffineProfile
