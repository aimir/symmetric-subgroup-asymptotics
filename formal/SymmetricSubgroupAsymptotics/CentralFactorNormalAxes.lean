import SymmetricSubgroupAsymptotics.CentralBinaryProductNormalAxes

/-! The checked minimal self-centralizing core argument works with any
second factor. The core lies in the first factor and every normal subgroup
missing it lies in the literal second axis. Commutativity of that axis is
only needed by later socle type-sharing, not by this dichotomy. -/

set_option autoImplicit false
noncomputable section
open scoped Classical commutatorElement

namespace SymmetricSubgroupAsymptotics

namespace CentralBinaryProductCore

variable {L : Type*} [Group L] (D : CentralBinaryProductCore L)
variable (C : Type*) [Group C]

/-- The natural layer in the first factor. -/
def productCore : Subgroup (L × C) := D.V.prod ⊥

/-- The literal second factor. It is central when C is commutative. -/
def productCentral (_D : CentralBinaryProductCore L) (C : Type*) [Group C] :
    Subgroup (L × C) :=
  (⊥ : Subgroup L).prod ⊤

@[simp] theorem mem_productCore (x : L × C) :
    x ∈ D.productCore C ↔ x.1 ∈ D.V ∧ x.2 = 1 := by
  change (x.1 ∈ D.V ∧ x.2 ∈ (⊥ : Subgroup C)) ↔ _
  simp only [Subgroup.mem_bot]

@[simp] theorem mem_productCentral (x : L × C) :
    x ∈ D.productCentral C ↔ x.1 = 1 := by
  change (x.1 ∈ (⊥ : Subgroup L) ∧ x.2 ∈ (⊤ : Subgroup C)) ↔ _
  simp only [Subgroup.mem_bot, Subgroup.mem_top, and_true]

instance productCore_normal : (D.productCore C).Normal where
  conj_mem x hx g := by
    apply (D.mem_productCore C _).mpr
    constructor
    · exact (inferInstance : D.V.Normal).conj_mem x.1 hx.1 g.1
    · change g.2 * x.2 * g.2⁻¹ = 1
      rw [hx.2]
      simp

instance productCentral_normal : (D.productCentral C).Normal where
  conj_mem x hx g := by
    apply (D.mem_productCentral C _).mpr
    simp [((D.mem_productCentral C x).mp hx)]

theorem productCore_minimal
    (W : Subgroup (L × C)) (hW : W.Normal) (hWV : W ≤ D.productCore C) :
    W = ⊥ ∨ W = D.productCore C := by
  let π : L × C →* L := MonoidHom.fst L C
  have hmapNormal : (W.map π).Normal := hW.map π Prod.fst_surjective
  have hmapV : W.map π ≤ D.V := by
    rintro x ⟨w, hw, rfl⟩
    exact ((D.mem_productCore C w).mp (hWV hw)).1
  rcases D.minimal (W.map π) hmapNormal hmapV with hbot | htop
  · left
    rw [eq_bot_iff]
    intro w hw
    have hwfst : w.1 = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← hbot]
      exact ⟨w, hw, rfl⟩
    have hwsnd : w.2 = 1 := ((D.mem_productCore C w).mp (hWV hw)).2
    exact Subgroup.mem_bot.mpr (Prod.ext hwfst hwsnd)
  · right
    apply le_antisymm hWV
    intro v hv
    obtain ⟨w, hwW, hfst⟩ : ∃ w ∈ W, w.1 = v.1 := by
      have hvmap : v.1 ∈ W.map π := by
        rw [htop]
        exact ((D.mem_productCore C v).mp hv).1
      rcases hvmap with ⟨w, hwW, hw⟩
      exact ⟨w, hwW, hw⟩
    have hwsnd : w.2 = 1 := ((D.mem_productCore C w).mp (hWV hwW)).2
    have hvsnd : v.2 = 1 := ((D.mem_productCore C v).mp hv).2
    have hwv : w = v := Prod.ext hfst (hwsnd.trans hvsnd.symm)
    rwa [← hwv]

/-- Every normal subgroup either contains the actual first-factor core
or lies in the actual second factor. -/
theorem normal_contains_productCore_or_le_productCentral
    (N : Subgroup (L × C)) (hN : N.Normal) :
    D.productCore C ≤ N ∨ N ≤ D.productCentral C := by
  let W := N ⊓ D.productCore C
  have hW : W.Normal := Subgroup.normal_inf_normal N (D.productCore C)
  rcases D.productCore_minimal C W hW inf_le_right with hbot | htop
  · right
    intro n hn
    have hnCentralizesCore : ∀ v ∈ D.productCore C, n * v = v * n := by
      intro v hv
      have hcN : n * v * n⁻¹ * v⁻¹ ∈ N := by
        have hconj : v * n⁻¹ * v⁻¹ ∈ N :=
          hN.conj_mem n⁻¹ (N.inv_mem hn) v
        simpa only [mul_assoc] using N.mul_mem hn hconj
      have hcV : n * v * n⁻¹ * v⁻¹ ∈ D.productCore C := by
        have hconj : n * v * n⁻¹ ∈ D.productCore C :=
          (inferInstance : (D.productCore C).Normal).conj_mem v hv n
        simpa only [mul_assoc] using (D.productCore C).mul_mem hconj ((D.productCore C).inv_mem hv)
      have hcommW : n * v * n⁻¹ * v⁻¹ ∈ W := ⟨hcN, hcV⟩
      rw [hbot] at hcommW
      have hc1 : n * v * n⁻¹ * v⁻¹ = 1 := Subgroup.mem_bot.mp hcommW
      calc
        n * v = (n * v * n⁻¹ * v⁻¹) * (v * n) := by group
        _ = v * n := by rw [hc1, one_mul]
    have hnV : n.1 ∈ D.V := by
      apply D.selfCentralizing
      intro v hv
      have hcomm := hnCentralizesCore (v, 1) ((D.mem_productCore C _).mpr ⟨hv, rfl⟩)
      exact congrArg Prod.fst hcomm
    have hnCentralizesAll : ∀ x : L, x * n.1 = n.1 * x := by
      intro x
      let c : L × C := (n * (x, 1) * n⁻¹ * (x, 1)⁻¹)
      have hcN : c ∈ N := by
        have hconj : (x, 1) * n⁻¹ * (x, 1)⁻¹ ∈ N :=
          hN.conj_mem n⁻¹ (N.inv_mem hn) (x, 1)
        change n * (x, 1) * n⁻¹ * (x, 1)⁻¹ ∈ N
        simpa only [mul_assoc] using N.mul_mem hn hconj
      have hcV : c ∈ D.productCore C := by
        apply (D.mem_productCore C c).mpr
        constructor
        · change n.1 * x * n.1⁻¹ * x⁻¹ ∈ D.V
          have hconj : x * n.1⁻¹ * x⁻¹ ∈ D.V :=
            (inferInstance : D.V.Normal).conj_mem n.1⁻¹ (D.V.inv_mem hnV) x
          simpa only [mul_assoc] using D.V.mul_mem hnV hconj
        · simp [c]
      have hcW : c ∈ W := ⟨hcN, hcV⟩
      rw [hbot] at hcW
      have hc1 : c = 1 := Subgroup.mem_bot.mp hcW
      have hfst := congrArg Prod.fst hc1
      change n.1 * x * n.1⁻¹ * x⁻¹ = 1 at hfst
      have hnx : n.1 * x = x * n.1 := by
        calc
          n.1 * x = (n.1 * x * n.1⁻¹ * x⁻¹) * (x * n.1) := by group
          _ = x * n.1 := by rw [hfst, one_mul]
      exact hnx.symm
    have hn1 : n.1 = 1 :=
      D.noFixed n.1 hnV (fun x => hnCentralizesAll x)
    exact (D.mem_productCentral C n).mpr hn1
  · left
    rw [← htop]
    exact inf_le_left

end CentralBinaryProductCore
end SymmetricSubgroupAsymptotics

end
