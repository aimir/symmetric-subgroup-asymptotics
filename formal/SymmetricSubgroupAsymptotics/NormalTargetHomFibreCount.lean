import SymmetricSubgroupAsymptotics.MarkedC4GeneratorNumbers
import SymmetricSubgroupAsymptotics.CentralizingHomCount

/-! Literal homomorphism fibres over a normal target quotient. Centrality
is unnecessary when the source's ordinary generating set is retained:
the values on those generators lie in prescribed normal-subgroup cosets.
No assertion that pointwise differences are homomorphisms is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.NormalTargetHomFibreCount

open MarkedC4

variable {G Q : Type*} [Group G] [Group Q] [Finite G] [Finite Q]

local instance : Finite (G →* Q) :=
  Finite.of_injective (fun f : G →* Q => (f : G → Q)) DFunLike.coe_injective

/-- A fixed quotient map leaves at most one normal-target coset per
ordinary source generator, including nonsplit and empty fibres. -/
theorem fibre_card_le (Z : Subgroup Q) [Z.Normal] (β : G →* Q ⧸ Z) :
    Nat.card {f : G →* Q // (QuotientGroup.mk' Z).comp f = β} ≤
      (Nat.card Z) ^ genRank G := by
  let F := {f : G →* Q // (QuotientGroup.mk' Z).comp f = β}
  by_cases hF : Nonempty F
  · obtain ⟨f₀⟩ := hF
    obtain ⟨S, hS, hgen⟩ := genRank_spec (G := G)
    have hmem (f : F) (x : G) : f.1 x * (f₀.1 x)⁻¹ ∈ Z := by
      apply (QuotientGroup.eq_one_iff (N := Z) _).mp
      change QuotientGroup.mk' Z (f.1 x * (f₀.1 x)⁻¹) = 1
      have hf := DFunLike.congr_fun f.2 x
      have hf₀ := DFunLike.congr_fun f₀.2 x
      change QuotientGroup.mk' Z (f.1 x) = β x at hf
      change QuotientGroup.mk' Z (f₀.1 x) = β x at hf₀
      rw [map_mul, map_inv, hf, hf₀, mul_inv_cancel]
    let code : F → (S → Z) := fun f s => ⟨f.1 s * (f₀.1 s)⁻¹, hmem f s⟩
    have hinj : Function.Injective code := by
      intro f g he
      apply Subtype.ext
      apply MonoidHom.eq_of_eqOn_dense hgen
      intro x hx
      have h := congrArg Subtype.val (congrFun he ⟨x, hx⟩)
      change f.1 x * (f₀.1 x)⁻¹ = g.1 x * (f₀.1 x)⁻¹ at h
      exact mul_right_cancel h
    calc
      Nat.card F ≤ Nat.card (S → Z) := Nat.card_le_card_of_injective code hinj
      _ = (Nat.card Z) ^ genRank G := by
        rw [Nat.card_fun, show Nat.card S = S.card from by
          rw [Nat.card_eq_fintype_card, Fintype.card_coe], hS]
  · letI : IsEmpty F := not_nonempty_iff.mp hF
    simp only [Nat.card_of_isEmpty, zero_le]

/-- All selected maps whose same original subgroup maps into a fixed
normal target subgroup. The source subgroup need not be normal. -/
theorem selected_card_le (C : Subgroup G) (Z : Subgroup Q) [Z.Normal]
    (P : (G →* Q) → Prop)
    (himage : ∀ f, P f → ∀ c ∈ C, f c ∈ Z) :
    Nat.card {f : G →* Q // P f} ≤
      (Nat.card (Q ⧸ Z)) ^ C.index * (Nat.card Z) ^ genRank G := by
  let F := {f : G →* Q // P f}
  let T := {β : G →* Q ⧸ Z // C ≤ β.ker}
  let π : F → T := fun f =>
    ⟨(QuotientGroup.mk' Z).comp f.1, by
      intro c hc
      exact (QuotientGroup.eq_one_iff (N := Z) _).mpr (himage f.1 f.2 c hc)⟩
  letI : Fintype T := Fintype.ofFinite T
  have hfibre (β : T) : Nat.card {f : F // π f = β} ≤
      (Nat.card Z) ^ genRank G := by
    let j : {f : F // π f = β} →
        {f : G →* Q // (QuotientGroup.mk' Z).comp f = β.1} :=
      fun f => ⟨f.1.1, congrArg Subtype.val f.2⟩
    have hj : Function.Injective j := by
      intro f g he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : {f : G →* Q // (QuotientGroup.mk' Z).comp f = β.1} => z.1) he
    exact (Nat.card_le_card_of_injective j hj).trans (fibre_card_le Z β.1)
  calc
    Nat.card F = Nat.card (Σ β : T, {f : F // π f = β}) :=
      (Nat.card_congr (Equiv.sigmaFiberEquiv π)).symm
    _ = ∑ β : T, Nat.card {f : F // π f = β} := Nat.card_sigma
    _ ≤ ∑ _β : T, (Nat.card Z) ^ genRank G :=
      Finset.sum_le_sum (fun β _ => hfibre β)
    _ = Nat.card T * (Nat.card Z) ^ genRank G := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_eq_nat_card]
      rfl
    _ ≤ _ := Nat.mul_le_mul_right _
      (CentralizingHomCount.quotientHom_card_le (R := Q ⧸ Z) C)

end SymmetricSubgroupAsymptotics.NormalTargetHomFibreCount
