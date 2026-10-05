import SymmetricSubgroupAsymptotics.Non2PreE7SmallModelToolkit

/-!
# Normal axes in a product with one central binary factor

This is the structural half of the three-pair `A4 × C2` and `S4 × C2`
rows.  Let `V` be the natural Klein subgroup in `L`.  Minimality,
self-centralization, and the absence of a fixed point in `V` imply that a
normal subgroup of `L × C2` either contains `V × 1` or lies in the central
factor `1 × C2`.  No finite catalogue calculation enters this dichotomy.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical commutatorElement

namespace SymmetricSubgroupAsymptotics

private abbrev C2 := Multiplicative (ZMod 2)

/-- The intrinsic hypotheses on the natural Klein layer used by both `A4`
and `S4`. -/
structure CentralBinaryProductCore (L : Type*) [Group L] where
  V : Subgroup L
  [normalV : V.Normal]
  minimal : ∀ W : Subgroup L, W.Normal → W ≤ V → W = ⊥ ∨ W = V
  selfCentralizing : ∀ x : L, (∀ v ∈ V, x * v = v * x) → x ∈ V
  noFixed : ∀ v ∈ V, (∀ x : L, x * v = v * x) → v = 1

attribute [instance] CentralBinaryProductCore.normalV

namespace CentralBinaryProductCore

variable {L : Type*} [Group L] (D : CentralBinaryProductCore L)

/-- The natural layer in the first factor. -/
def core : Subgroup (L × C2) := D.V.prod ⊥

/-- The central binary factor. -/
def central (_D : CentralBinaryProductCore L) : Subgroup (L × C2) :=
  (⊥ : Subgroup L).prod ⊤

@[simp] theorem mem_core (x : L × C2) :
    x ∈ D.core ↔ x.1 ∈ D.V ∧ x.2 = 1 := by
  change (x.1 ∈ D.V ∧ x.2 ∈ (⊥ : Subgroup C2)) ↔ _
  simp only [Subgroup.mem_bot]

@[simp] theorem mem_central (x : L × C2) :
    x ∈ D.central ↔ x.1 = 1 := by
  change (x.1 ∈ (⊥ : Subgroup L) ∧ x.2 ∈ (⊤ : Subgroup C2)) ↔ _
  simp only [Subgroup.mem_bot, Subgroup.mem_top, and_true]

instance core_normal : D.core.Normal where
  conj_mem x hx g := by
    apply (D.mem_core _).mpr
    constructor
    · exact (inferInstance : D.V.Normal).conj_mem x.1 hx.1 g.1
    · change g.2 * x.2 * g.2⁻¹ = 1
      rw [hx.2]
      simp

instance central_normal : D.central.Normal where
  conj_mem x hx g := by
    apply (D.mem_central _).mpr
    simp [((D.mem_central x).mp hx)]

private theorem core_minimal
    (W : Subgroup (L × C2)) (hW : W.Normal) (hWV : W ≤ D.core) :
    W = ⊥ ∨ W = D.core := by
  let π : L × C2 →* L := MonoidHom.fst L C2
  have hmapNormal : (W.map π).Normal := hW.map π Prod.fst_surjective
  have hmapV : W.map π ≤ D.V := by
    rintro x ⟨w, hw, rfl⟩
    exact ((D.mem_core w).mp (hWV hw)).1
  rcases D.minimal (W.map π) hmapNormal hmapV with hbot | htop
  · left
    rw [eq_bot_iff]
    intro w hw
    have hwfst : w.1 = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← hbot]
      exact ⟨w, hw, rfl⟩
    have hwsnd : w.2 = 1 := ((D.mem_core w).mp (hWV hw)).2
    exact Subgroup.mem_bot.mpr (Prod.ext hwfst hwsnd)
  · right
    apply le_antisymm hWV
    intro v hv
    obtain ⟨w, hwW, hfst⟩ : ∃ w ∈ W, w.1 = v.1 := by
      have hvmap : v.1 ∈ W.map π := by
        rw [htop]
        exact ((D.mem_core v).mp hv).1
      rcases hvmap with ⟨w, hwW, hw⟩
      exact ⟨w, hwW, hw⟩
    have hwsnd : w.2 = 1 := ((D.mem_core w).mp (hWV hwW)).2
    have hvsnd : v.2 = 1 := ((D.mem_core v).mp hv).2
    have hwv : w = v := Prod.ext hfst (hwsnd.trans hvsnd.symm)
    rwa [← hwv]

/-- Every normal axis either contains the natural Klein layer or is confined
to the central binary factor. -/
theorem normal_contains_core_or_le_central
    (N : Subgroup (L × C2)) (hN : N.Normal) :
    D.core ≤ N ∨ N ≤ D.central := by
  let W := N ⊓ D.core
  have hW : W.Normal := Subgroup.normal_inf_normal N D.core
  rcases D.core_minimal W hW inf_le_right with hbot | htop
  · right
    intro n hn
    have hnCentralizesCore : ∀ v ∈ D.core, n * v = v * n := by
      intro v hv
      have hcN : n * v * n⁻¹ * v⁻¹ ∈ N := by
        have hconj : v * n⁻¹ * v⁻¹ ∈ N :=
          hN.conj_mem n⁻¹ (N.inv_mem hn) v
        simpa only [mul_assoc] using N.mul_mem hn hconj
      have hcV : n * v * n⁻¹ * v⁻¹ ∈ D.core := by
        have hconj : n * v * n⁻¹ ∈ D.core :=
          (inferInstance : D.core.Normal).conj_mem v hv n
        simpa only [mul_assoc] using D.core.mul_mem hconj (D.core.inv_mem hv)
      have hcommW : n * v * n⁻¹ * v⁻¹ ∈ W := ⟨hcN, hcV⟩
      rw [hbot] at hcommW
      have hc1 : n * v * n⁻¹ * v⁻¹ = 1 := Subgroup.mem_bot.mp hcommW
      calc
        n * v = (n * v * n⁻¹ * v⁻¹) * (v * n) := by group
        _ = v * n := by rw [hc1, one_mul]
    have hnV : n.1 ∈ D.V := by
      apply D.selfCentralizing
      intro v hv
      have hcomm := hnCentralizesCore (v, 1) ((D.mem_core _).mpr ⟨hv, rfl⟩)
      exact congrArg Prod.fst hcomm
    have hnCentralizesAll : ∀ x : L, x * n.1 = n.1 * x := by
      intro x
      let c : L × C2 := (n * (x, 1) * n⁻¹ * (x, 1)⁻¹)
      have hcN : c ∈ N := by
        have hconj : (x, 1) * n⁻¹ * (x, 1)⁻¹ ∈ N :=
          hN.conj_mem n⁻¹ (N.inv_mem hn) (x, 1)
        change n * (x, 1) * n⁻¹ * (x, 1)⁻¹ ∈ N
        simpa only [mul_assoc] using N.mul_mem hn hconj
      have hcV : c ∈ D.core := by
        apply (D.mem_core c).mpr
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
    exact (D.mem_central n).mpr hn1
  · left
    rw [← htop]
    exact inf_le_left

end CentralBinaryProductCore
end SymmetricSubgroupAsymptotics

end
