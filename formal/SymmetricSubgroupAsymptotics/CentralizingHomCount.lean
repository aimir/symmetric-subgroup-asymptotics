import SymmetricSubgroupAsymptotics.BinaryTargetOrderEnvelope
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.Coset.Card

/-! Counting actual homomorphisms that send an original subgroup into the
actual target center. The quotient map is encoded on original left cosets;
each fibre consists of central differences. The subgroup need not be normal.
For a binary target the only source-dependent exponential factor is the
order of the actual target center raised to the original binary head rank.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics
namespace CentralizingHomCount

local instance homFinite {G Q : Type*} [Group G] [Group Q] [Finite G] [Finite Q] :
    Finite (G →* Q) := Finite.of_injective (fun f : G →* Q => (f : G → Q))
    DFunLike.coe_injective

section Fibre
variable {G Q : Type*} [Group G] [Group Q]
    (Z : Subgroup Q) [Z.Normal] (hZ : Z ≤ Subgroup.center Q)
    (β : G →* Q ⧸ Z)

private theorem difference_mem
    (f f₀ : {f : G →* Q // (QuotientGroup.mk' Z).comp f = β}) (x : G) :
    f.1 x * (f₀.1 x)⁻¹ ∈ Z := by
  apply (QuotientGroup.eq_one_iff (N := Z) _).mp
  change QuotientGroup.mk' Z (f.1 x * (f₀.1 x)⁻¹) = 1
  have hf : QuotientGroup.mk' Z (f.1 x)=β x := DFunLike.congr_fun f.2 x
  have hf₀ : QuotientGroup.mk' Z (f₀.1 x)=β x := DFunLike.congr_fun f₀.2 x
  rw [map_mul,map_inv,hf,hf₀,mul_inv_cancel]

private def difference
    (f₀ f : {f : G →* Q // (QuotientGroup.mk' Z).comp f = β}) : G →* Z where
  toFun x := ⟨f.1 x * (f₀.1 x)⁻¹, difference_mem Z β f f₀ x⟩
  map_one' := by
    apply Subtype.ext
    simp only [map_one, inv_one, mul_one]
    rfl
  map_mul' x y := by
    apply Subtype.ext
    have hc : Commute (f₀.1 x) (f.1 y * (f₀.1 y)⁻¹) :=
      Subgroup.mem_center_iff.mp (hZ (difference_mem Z β f f₀ y)) (f₀.1 x)
    change f.1 (x*y) * (f₀.1 (x*y))⁻¹ =
      (f.1 x * (f₀.1 x)⁻¹) * (f.1 y * (f₀.1 y)⁻¹)
    calc
      _ = (f.1 x * (f₀.1 x)⁻¹) *
          (f₀.1 x * (f.1 y * (f₀.1 y)⁻¹) * (f₀.1 x)⁻¹) := by
        rw [map_mul, map_mul]
        group
      _ = _ := by rw [hc.mul_inv_cancel]

include hZ in
/-- Every nonempty original quotient-map fibre admits an injective central
homomorphism difference, without a group section or splitting assumption. -/
theorem fibre_card_le [Finite G] [Finite Q] :
    Nat.card {f : G →* Q // (QuotientGroup.mk' Z).comp f = β} ≤
      Nat.card (G →* Z) := by
  by_cases hn : Nonempty {f : G →* Q // (QuotientGroup.mk' Z).comp f = β}
  · obtain ⟨f₀⟩ := hn
    apply Nat.card_le_card_of_injective (difference Z hZ β f₀)
    intro f g he
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    have h := congrArg Subtype.val (DFunLike.congr_fun he x)
    change f.1 x * (f₀.1 x)⁻¹ = g.1 x * (f₀.1 x)⁻¹ at h
    exact mul_right_cancel h
  · letI := not_nonempty_iff.mp hn
    simp
end Fibre

section Cosets
variable {G R : Type*} [Group G] [Group R] (C : Subgroup G)

/-- A homomorphism vanishing on the original subgroup is constant on its
left cosets, even if the subgroup is not normal. -/
def cosetCode (β : {β : G →* R // C ≤ β.ker}) : G ⧸ C → R :=
  Quotient.lift β.1 (by
    intro a b hab
    have hz : β.1 (a⁻¹*b)=1 := β.2 (QuotientGroup.leftRel_apply.mp hab)
    rw [map_mul, map_inv, inv_mul_eq_one] at hz
    exact hz)

theorem cosetCode_injective : Function.Injective (cosetCode (R := R) C) := by
  intro β γ he
  apply Subtype.ext
  apply MonoidHom.ext
  intro g
  exact congrFun he (QuotientGroup.mk g)

/-- Count quotient maps by their values on the same original cosets. -/
theorem quotientHom_card_le [Finite G] [Finite R] :
    Nat.card {β : G →* R // C ≤ β.ker} ≤ (Nat.card R)^C.index := by
  have h := Nat.card_le_card_of_injective _ (cosetCode_injective (R := R) C)
  simpa only [Nat.card_fun, ← C.index_eq_card] using h
end Cosets

section Selected
variable {G Q : Type*} [Group G] [Group Q] [Finite G] [Finite Q]
    (C : Subgroup G) (P : (G →* Q) → Prop)
    (hcentral : ∀ f, P f → ∀ c ∈ C, f c ∈ Subgroup.center Q)

include hcentral

/-- The exact quotient-center fibres of the selected actual maps. -/
theorem selected_card_le :
    Nat.card {f : G →* Q // P f} ≤
      (Nat.card (Q ⧸ Subgroup.center Q))^C.index *
        Nat.card (G →* Subgroup.center Q) := by
  let F := {f : G →* Q // P f}
  let T := {β : G →* Q ⧸ Subgroup.center Q // C ≤ β.ker}
  let π : F → T := fun f =>
    ⟨(QuotientGroup.mk' (Subgroup.center Q)).comp f.1, by
      intro c hc
      exact (QuotientGroup.eq_one_iff (N := Subgroup.center Q) _).mpr
        (hcentral f.1 f.2 c hc)⟩
  letI : Fintype T := Fintype.ofFinite T
  have hfibre (β : T) : Nat.card {f : F // π f=β} ≤
      Nat.card (G →* Subgroup.center Q) := by
    let j : {f : F // π f=β} →
        {f : G →* Q // (QuotientGroup.mk' (Subgroup.center Q)).comp f=β.1} :=
      fun f => ⟨f.1.1, congrArg Subtype.val f.2⟩
    have hj : Function.Injective j := by
      intro f g he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg
        (fun t : {f : G →* Q // (QuotientGroup.mk' (Subgroup.center Q)).comp f=β.1} => t.1) he
    exact (Nat.card_le_card_of_injective j hj).trans
      (fibre_card_le (Subgroup.center Q) le_rfl β.1)
  calc
    _ = Nat.card (Σ β : T, {f : F // π f=β}) :=
      (Nat.card_congr (Equiv.sigmaFiberEquiv π)).symm
    _ = ∑ β : T, Nat.card {f : F // π f=β} := Nat.card_sigma
    _ ≤ ∑ _β : T, Nat.card (G →* Subgroup.center Q) :=
      Finset.sum_le_sum (fun β _ => hfibre β)
    _ = Nat.card T * Nat.card (G →* Subgroup.center Q) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_eq_nat_card]
      rfl
    _ ≤ _ := Nat.mul_le_mul_right _ (quotientHom_card_le (R := Q ⧸ Subgroup.center Q) C)

/-- For a finite binary target, all source growth in this bound has the
required center-order slope. No rank of a subgroup of G is substituted. -/
theorem selected_binary_card_le (hQ : IsPGroup 2 Q) :
    Nat.card {f : G →* Q // P f} ≤
      (Nat.card Q)^C.index * (Nat.card (Subgroup.center Q))^(binaryCharacterRank G) := by
  have hquot : Nat.card (Q ⧸ Subgroup.center Q) ≤ Nat.card Q :=
    Nat.card_le_card_of_surjective (QuotientGroup.mk' (Subgroup.center Q))
      (QuotientGroup.mk'_surjective _)
  obtain ⟨a,ha⟩ := (hQ.to_subgroup (Subgroup.center Q)).exists_card_eq
  have hz : Nat.card (G →* Subgroup.center Q) ≤
      (Nat.card (Subgroup.center Q))^(binaryCharacterRank G) := by
    rw [ha, ← pow_mul]
    exact binaryTargetOrder_hom_card_le_of_card_pow_two a ha
  exact (selected_card_le C P hcentral).trans
    (Nat.mul_le_mul (pow_le_pow_left₀ (Nat.zero_le _) hquot C.index) hz)
end Selected

/-- If the displayed original subgroup maps onto Q, its actual
centralizer maps into the center of Q. -/
theorem centralizer_image_le_center {G Q : Type*} [Group G] [Group Q]
    (S : Subgroup G) (f : G →* Q) (hf : Function.Surjective (f.comp S.subtype)) :
    ∀ c ∈ Subgroup.centralizer (S : Set G), f c ∈ Subgroup.center Q := by
  intro c hc
  apply Subgroup.mem_center_iff.mpr
  intro q
  obtain ⟨s,rfl⟩ := hf q
  change f (s : G) * f c = f c * f (s : G)
  rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.mp hc) s s.2]

/-- A useful unconditional instance: all literal maps that are onto on
one fixed original subgroup. Its centralizer index controls only a constant. -/
theorem surjective_restriction_binary_card_le
    {G Q : Type*} [Group G] [Group Q] [Finite G] [Finite Q]
    (S : Subgroup G) (hQ : IsPGroup 2 Q) :
    Nat.card {f : G →* Q // Function.Surjective (f.comp S.subtype)} ≤
      (Nat.card Q)^(Subgroup.centralizer (S : Set G)).index *
        (Nat.card (Subgroup.center Q))^(binaryCharacterRank G) :=
  selected_binary_card_le (Subgroup.centralizer (S : Set G)) _
    (fun f hf => centralizer_image_le_center S f hf) hQ

end CentralizingHomCount
end SymmetricSubgroupAsymptotics
