import SymmetricSubgroupAsymptotics.BinaryMarkedTailImage
import Mathlib.Tactic.Convert

/-! The actual family-level induction step. The tail family is an arbitrary
predicate on literal subgroups of the original B. Original survival is
transported by exact reconstruction, and every marked sum uses the same
actual tail L before applying the checked fixed-tail Goursat peel.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryMarkedTailFamily

open FullSubdirectGoursat BinaryMarkedGoursatPeel

variable {A B : Type} [Group A] [Group B]

abbrev OriginalFamily (A B : Type) [Group A] [Group B] (R : Subgroup B → Prop) :=
  {H : SubdirectTailImage.FirstFull A B // R (SubdirectTailImage.tail H.1)}

abbrev CoreFamily (A B : Type) [Group A] [Group B] (R : Subgroup B → Prop) :=
  Σ L : {L : Subgroup B // R L}, Full A L.1

variable (R : Subgroup B → Prop)

def code (H : OriginalFamily A B R) : CoreFamily A B R :=
  ⟨⟨SubdirectTailImage.tail H.1.1,H.2⟩,SubdirectTailImage.full H.1.1 H.1.2⟩

def decode (d : CoreFamily A B R) : Subgroup (A × B) :=
  SubdirectTailImage.decode ⟨d.1.1,d.2⟩

@[simp] theorem decode_code (H : OriginalFamily A B R) : decode R (code R H) = H.1.1 :=
  SubdirectTailImage.core_map H.1.1

theorem code_injective : Function.Injective (code (A := A) R) := by
  intro H K he
  apply Subtype.ext
  apply Subtype.ext
  exact (decode_code R H).symm.trans ((congrArg (decode R) he).trans (decode_code R K))

def originalAxis (H : OriginalFamily A B R) : NormalAxis A :=
  ⟨H.1.1.goursatFst,Subgroup.normal_goursatFst H.1.2⟩

theorem code_axis (H : OriginalFamily A B R) :
    axis (code R H).2 = originalAxis R H :=
  Subtype.ext (SubdirectTailImage.core_axis H.1.1)

section Finite
variable [Finite A] [Finite B]

local instance subgroupFinite {G : Type*} [Group G] [Finite G] : Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

attribute [local instance] Fintype.ofFinite

theorem code_mark (H : OriginalFamily A B R) (x y z : ℝ) :
    mark (code R H).2.1 x y z = mark H.1.1 x y z :=
  (original_mark_eq_core H.1.1 x y z).symm

/-- The first stage retains the original survival test through the exact
decoder. Any enlargement is only the injective original-family embedding. -/
theorem survival_sum_le_cores
    (P : Subgroup (A × B) → Prop) (w : Subgroup B → NormalAxis A → ℝ)
    (hw : ∀ L, R L → ∀ N, 0 ≤ w L N) (x y z : ℝ) :
    (∑ H : OriginalFamily A B R, if P H.1.1 then
      w (SubdirectTailImage.tail H.1.1) (originalAxis R H)*mark H.1.1 x y z else 0) ≤
      ∑ d : CoreFamily A B R, if P (decode R d) then
        w d.1.1 (axis d.2)*mark d.2.1 x y z else 0 := by
  classical
  let W (d : CoreFamily A B R) := if P (decode R d) then
    w d.1.1 (axis d.2)*mark d.2.1 x y z else 0
  have hW (d : CoreFamily A B R) : 0 ≤ W d := by
    dsimp only [W]
    split_ifs
    · exact mul_nonneg (hw d.1.1 d.1.2 (axis d.2)) (mark_nonneg d.2.1 x y z)
    · exact le_rfl
  have he (H : OriginalFamily A B R) : W (code R H) =
      (if P H.1.1 then w (SubdirectTailImage.tail H.1.1) (originalAxis R H)*
        mark H.1.1 x y z else 0) := by
    dsimp only [W]
    rw [decode_code,code_axis,code_mark]
    rfl
  calc
    _ = ∑ H : OriginalFamily A B R, W (code R H) :=
      Finset.sum_congr rfl (fun H _ => (he H).symm)
    _ = ∑ d ∈ Finset.univ.image (code R), W d := by
      rw [Finset.sum_image]
      intro H _ K _ h
      exact code_injective R h
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun d _ _ => hW d)

/-- The sigma decomposition is isolated from the marked inequalities so
that elaboration does not unfold the dependent subgroup marks during a rewrite. -/
theorem core_sum_eq_iterated
    (P : Subgroup (A × B) → Prop) (w : Subgroup B → NormalAxis A → ℝ)
    (x y z : ℝ) :
    (∑ d : CoreFamily A B R, if P (decode R d) then
      w d.1.1 (axis d.2)*mark d.2.1 x y z else 0) =
      ∑ L : {L : Subgroup B // R L}, ∑ K : Full A L.1,
        if P (decode R ⟨L,K⟩) then w L.1 (axis K)*mark K.1 x y z else 0 :=
  Fintype.sum_sigma _

/-- The fixed-tail theorem is applied to the exact selected subgroup,
with survival still evaluated on its original decoded subgroup. -/
theorem core_tail_weighted_peel (hA : IsPGroup 2 A)
    (L : {L : Subgroup B // R L}) (hL : IsPGroup 2 L.1)
    (P : Subgroup (A × B) → Prop) (w : Subgroup B → NormalAxis A → ℝ)
    (hw : ∀ N, 0 ≤ w L.1 N) (x y z : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (∑ K : Full A L.1, if P (decode R ⟨L,K⟩) then
      w L.1 (axis K)*mark K.1 x y z else 0) ≤
      ∑ N : NormalAxis A,
        w L.1 N * polynomial N L.1 * (2 : ℝ)^(cost N x y z) *
          mark L.1 (x+(centerSlope N : ℝ)) (y+(derivedSlope N : ℝ)) z := by
  have h := surviving_weighted_peel (A := A) (B := L.1) hA hL
    (fun K : Full A L.1 => P (decode R ⟨L,K⟩)) (w L.1) hw x y z hy hz
  convert (config := { transparency := .reducible }) h

theorem cores_sum_le_peels (hA : IsPGroup 2 A)
    (hR : ∀ L : Subgroup B, R L → IsPGroup 2 L)
    (P : Subgroup (A × B) → Prop) (w : Subgroup B → NormalAxis A → ℝ)
    (hw : ∀ L, R L → ∀ N, 0 ≤ w L N)
    (x y z : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (∑ d : CoreFamily A B R, if P (decode R d) then
      w d.1.1 (axis d.2)*mark d.2.1 x y z else 0) ≤
      ∑ L : {L : Subgroup B // R L}, ∑ N : NormalAxis A,
        w L.1 N * polynomial N L.1 * (2 : ℝ)^(cost N x y z) *
          mark L.1 (x+(centerSlope N : ℝ)) (y+(derivedSlope N : ℝ)) z := by
  apply (core_sum_eq_iterated R P w x y z).trans_le
  exact Finset.sum_le_sum (fun L _ =>
    core_tail_weighted_peel R hA L (hR L.1 L.2) P w (hw L.1 L.2) x y z hy hz)

/-- The finite family step is derived on each SAME literal L. The only
group-type input on a tail is that this actual subgroup is binary; the
tail-family predicate can specify full coordinate projections recursively. -/
theorem weighted_peel_family (hA : IsPGroup 2 A)
    (hR : ∀ L : Subgroup B, R L → IsPGroup 2 L)
    (P : Subgroup (A × B) → Prop) (w : Subgroup B → NormalAxis A → ℝ)
    (hw : ∀ L, R L → ∀ N, 0 ≤ w L N)
    (x y z : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (∑ H : OriginalFamily A B R, if P H.1.1 then
      w (SubdirectTailImage.tail H.1.1) (originalAxis R H)*mark H.1.1 x y z else 0) ≤
      ∑ L : {L : Subgroup B // R L}, ∑ N : NormalAxis A,
        w L.1 N * polynomial N L.1 * (2 : ℝ)^(cost N x y z) *
          mark L.1 (x+(centerSlope N : ℝ)) (y+(derivedSlope N : ℝ)) z :=
  (survival_sum_le_cores R P w hw x y z).trans
    (cores_sum_le_peels R hA hR P w hw x y z hy hz)

/-- For an actual binary ambient tail product, every literal tail subgroup
is automatically binary. No extra source-type certificate is required. -/
theorem weighted_peel_binary_ambient (hA : IsPGroup 2 A) (hB : IsPGroup 2 B)
    (P : Subgroup (A × B) → Prop) (w : Subgroup B → NormalAxis A → ℝ)
    (hw : ∀ L, R L → ∀ N, 0 ≤ w L N)
    (x y z : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (∑ H : OriginalFamily A B R, if P H.1.1 then
      w (SubdirectTailImage.tail H.1.1) (originalAxis R H)*mark H.1.1 x y z else 0) ≤
      ∑ L : {L : Subgroup B // R L}, ∑ N : NormalAxis A,
        w L.1 N * polynomial N L.1 * (2 : ℝ)^(cost N x y z) *
          mark L.1 (x+(centerSlope N : ℝ)) (y+(derivedSlope N : ℝ)) z :=
  weighted_peel_family R hA (fun L _ => hB.to_subgroup L) P w hw x y z hy hz

end Finite
end BinaryMarkedTailFamily
end SymmetricSubgroupAsymptotics
