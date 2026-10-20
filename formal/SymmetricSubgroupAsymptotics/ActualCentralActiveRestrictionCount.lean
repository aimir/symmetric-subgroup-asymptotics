import SymmetricSubgroupAsymptotics.ActualCentralInvariantLiftCount
import Mathlib.Logic.Equiv.Sum

/-! Actual equivariant restrictions to a central extension of repeated
scalar-four coordinates. The quotient-map fibre is retained before the
central character enlargement, so nonsplit targets are included. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.ActualCentralActiveRestrictionCount
open ScalarFourCentralActiveMaxCount
variable {F K : Type} [Group F] [Group K]

private theorem card_le_fibre_bound {X Y : Type} [Finite X] [Fintype Y]
    (f : X → Y) (m : ℕ) (hm : ∀ y : Y, Nat.card {x : X // f x = y} ≤ m) :
    Nat.card X≤Nat.card Y*m := by
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f),Nat.card_sigma]
  calc
    _ ≤ ∑ _y : Y, m := Finset.sum_le_sum (fun y _ => hm y)
    _ = _ := by simp [Nat.card_eq_fintype_card]

variable (alpha : F → F) (beta : K ≃* K) {c d : ℕ}
  (q : K →* (Fin d → ScalarFour))
  (hc : ∀ z : q.ker, ∀ k : K, (z : K)*k=k*(z : K))
  (hfixed : ∀ z : q.ker, beta (z : K)=(z : K))
  (hq : ∀ k j, q (beta k) j=scalarFourTwist 1 (q k j))
  (z : q.ker →* (Fin c → Binary)) (hz : Function.Injective z)

abbrev Restriction := {phi : F →* K // ∀ x, phi (alpha x)=beta (phi x)}

private def active (phi : Restriction alpha beta) (j : Fin d) : Twisted F alpha :=
  ⟨{ toFun := fun x => q (phi.val x) j
     map_one' := by rw [map_one,map_one]; rfl
     map_mul' := by intro x y; rw [map_mul,map_mul]; rfl },by
    intro x
    change q (phi.val (alpha x)) j=scalarFourTwist 1 (q (phi.val x) j)
    rw [phi.property,hq]⟩

private def activeHom (t : Fin d → Twisted F alpha) : F →* (Fin d → ScalarFour) where
  toFun x j := (t j).val x
  map_one' := by funext j; exact (t j).val.map_one
  map_mul' x y := by funext j; exact (t j).val.map_mul x y

include hc hfixed hq hz in
theorem restriction_card_le [Finite F] [Finite K] :
    Nat.card (Restriction alpha beta) ≤ 2^(max c d * binaryCharacterRank F) := by
  letI : Finite (F →* K) := Finite.of_injective
    (fun f : F →* K => (f : F → K)) DFunLike.coe_injective
  letI : Finite (F →* Binary) := Finite.of_injective
    (fun f : F →* Binary => (f : F → Binary)) DFunLike.coe_injective
  letI : Finite (F →* ScalarFour) := Finite.of_injective
    (fun f : F →* ScalarFour => (f : F → ScalarFour)) DFunLike.coe_injective
  letI : Fintype (Twisted F alpha) := Fintype.ofFinite _
  let project : Restriction alpha beta → Fin d → Twisted F alpha := active alpha beta q hq
  have hf (t : Fin d → Twisted F alpha) :
      Nat.card {phi // project phi=t}≤Nat.card (Invariant F alpha)^c := by
    let embed : {phi // project phi=t} →
        ActualCentralInvariantLiftCount.Fibre q alpha beta (activeHom alpha t) := fun phi =>
      ⟨phi.val.val,by
        constructor
        · apply MonoidHom.ext
          intro x
          funext j
          have he := congrArg Subtype.val (congrFun phi.property j)
          exact DFunLike.congr_fun he x
        · exact phi.val.property⟩
    have hi : Function.Injective embed := by
      intro phi chi h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun l : ActualCentralInvariantLiftCount.Fibre q alpha beta
        (activeHom alpha t) => l.val) h
    exact (Nat.card_le_card_of_injective embed hi).trans
      (ActualCentralInvariantLiftCount.fibre_card_le q alpha beta
        (activeHom alpha t) hc hfixed z hz)
  calc
    _ ≤ Nat.card (Fin d → Twisted F alpha)*Nat.card (Invariant F alpha)^c :=
      card_le_fibre_bound project _ hf
    _ = Nat.card (Invariant F alpha)^c*Nat.card (Twisted F alpha)^d := by
      rw [Nat.card_fun,Nat.card_fin,Nat.mul_comm]
    _ ≤ _ := max_card_le F alpha c d
end SymmetricSubgroupAsymptotics.ActualCentralActiveRestrictionCount
