import SymmetricSubgroupAsymptotics.ActualCentralLiftDifference
import SymmetricSubgroupAsymptotics.ScalarFourCentralActiveMaxCount

/-! An actual equivariant central-lift fibre has one invariant binary
character per coordinate of its actual kernel. No split is required. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.ActualCentralInvariantLiftCount
open ScalarFourCentralActiveMaxCount
variable {F K A : Type} [Group F] [Group K] [Group A]
  (q : K →* A) (alpha : F → F) (beta : K ≃* K) (eta : F →* A)

abbrev Fibre := {phi : F →* K // q.comp phi=eta ∧
  ∀ x, phi (alpha x)=beta (phi x)}

variable (hc : ∀ z : q.ker, ∀ k : K, (z : K)*k=k*(z : K))
  (hfixed : ∀ z : q.ker, beta (z : K)=(z : K))
  {c : ℕ} (z : q.ker →* (Fin c → Binary)) (hz : Function.Injective z)

private def coordinate (j : Fin c) : q.ker →* Binary where
  toFun v := z v j
  map_one' := congrFun z.map_one j
  map_mul' v w := congrFun (z.map_mul v w) j

include hc hfixed hz in
theorem fibre_card_le [Finite F] [Finite K] :
    Nat.card (Fibre q alpha beta eta) ≤
      Nat.card (Invariant F alpha)^c := by
  let L := Fibre q alpha beta eta
  by_cases hn : Nonempty L
  · let psi : L := Classical.choice hn
    let lift : L → ActualCentralLiftDifference.Lift q psi.val := fun phi =>
      ⟨phi.val,phi.property.1.trans psi.property.1.symm⟩
    let delta : L → (F →* q.ker) := fun phi =>
      ActualCentralLiftDifference.difference q hc psi.val (lift phi)
    have hdelta (phi : L) (x : F) : delta phi (alpha x)=delta phi x :=
      ActualCentralLiftDifference.difference_invariant q hc psi.val alpha beta
        psi.property.2 hfixed (lift phi) phi.property.2 x
    let enc : L → Fin c → Invariant F alpha := fun phi j =>
      ⟨(coordinate q z j).comp (delta phi),fun x =>
        congrArg (fun v : q.ker => z v j) (hdelta phi x)⟩
    have hi : Function.Injective enc := by
      intro phi chi h
      have hd : delta phi=delta chi := by
        apply MonoidHom.ext
        intro x
        apply hz
        funext j
        have hh := congrArg Subtype.val (congrFun h j)
        exact DFunLike.congr_fun hh x
      have hl := ActualCentralLiftDifference.difference_injective q hc psi.val hd
      exact Subtype.ext (congrArg
        (fun l : ActualCentralLiftDifference.Lift q psi.val => l.val) hl)
    letI : Finite (F →* Binary) := Finite.of_injective
      (fun f : F →* Binary => (f : F → Binary)) DFunLike.coe_injective
    calc Nat.card L ≤ Nat.card (Fin c → Invariant F alpha) :=
        Nat.card_le_card_of_injective enc hi
      _ = _ := by rw [Nat.card_fun,Nat.card_fin]
  · letI : IsEmpty L := not_nonempty_iff.mp hn
    change Nat.card L ≤ _
    rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _
end SymmetricSubgroupAsymptotics.ActualCentralInvariantLiftCount
