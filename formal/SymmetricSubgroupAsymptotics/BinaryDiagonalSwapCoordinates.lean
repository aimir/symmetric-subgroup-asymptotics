import SymmetricSubgroupAsymptotics.Non2PreE7C2Wreath
import SymmetricSubgroupAsymptotics.SemidirectAbelianCentralizer

/-!
# Two translation blocks with a diagonal action and a swap

The model retains the whole translation pair. Multiplying its two
coordinates gives an epimorphism onto the local semidirect product times
the swap group. For an elementary binary translation group, its kernel is
the diagonal translation copy. All statements are structural.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryDiagonalSwap

open SemidirectProduct

abbrev Binary := Multiplicative (ZMod 2)

variable {V R : Type} [CommGroup V] [Group R]
variable (φ : R →* MulAut V)

def diagonalAut (r : R) : MulAut (V × V) := (φ r).prodCongr (φ r)

def action : R × Binary →* MulAut (V × V) where
  toFun h := diagonalAut φ h.1 * C2Wreath.swapAut V h.2
  map_one' := by
    apply MulEquiv.ext
    intro v
    simp [diagonalAut]
    rfl
  map_mul' h k := by
    rcases h with ⟨r, c⟩
    rcases k with ⟨s, d⟩
    rcases C2Wreath.cases c with rfl | rfl <;>
      rcases C2Wreath.cases d with rfl | rfl
    all_goals
      apply MulEquiv.ext
      intro v
      apply Prod.ext <;>
        simp [diagonalAut, C2Wreath.swapAut, C2Wreath.gen_ne_one,
          C2Wreath.gen_mul_gen, map_mul] <;> rfl

abbrev Model := (V × V) ⋊[action φ] (R × Binary)
abbrev Local := V ⋊[φ] R

theorem action_one (r : R) (v : V × V) :
    action φ (r, 1) v = (φ r v.1, φ r v.2) := by
  simp [action, diagonalAut]
  rfl

theorem action_swap (r : R) (v : V × V) :
    action φ (r, C2Wreath.gen) v = (φ r v.2, φ r v.1) := by
  simp [action, diagonalAut, C2Wreath.swapAut_gen]
  rfl

theorem action_product (h : R × Binary) (v : V × V) :
    (action φ h v).1 * (action φ h v).2 = φ h.1 (v.1 * v.2) := by
  rcases h with ⟨r, c⟩
  rcases C2Wreath.cases c with rfl | rfl
  · rw [action_one, map_mul]
  · rw [action_swap, map_mul]
    exact mul_comm _ _

theorem action_injective [Nontrivial V] (hφ : Function.Injective φ) :
    Function.Injective (action φ) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨r, c⟩ h
  rcases C2Wreath.cases c with rfl | rfl
  · have hr : φ r = 1 := by
      apply MulEquiv.ext
      intro v
      have he := congrArg (fun f : MulAut (V × V) ↦ (f (v, 1)).1) h
      simpa only [action_one, MulAut.one_apply] using he
    exact Prod.ext (hφ (hr.trans φ.map_one.symm)) rfl
  · obtain ⟨v, hv⟩ := exists_ne (1 : V)
    have he := congrArg (fun f : MulAut (V × V) ↦ (f (v, 1)).1) h
    have hv1 : 1 = v := by
      simpa only [action_swap, map_one, MulAut.one_apply] using he
    exact (hv hv1.symm).elim

def projection : Model φ →* Local φ × Binary where
  toFun g := (⟨g.left.1 * g.left.2, g.right.1⟩, g.right.2)
  map_one' := by
    apply Prod.ext
    · apply SemidirectProduct.ext <;> simp
    · rfl
  map_mul' g h := by
    apply Prod.ext
    · apply SemidirectProduct.ext
      · change (g.left.1 * (action φ g.right h.left).1) *
            (g.left.2 * (action φ g.right h.left).2) =
          (g.left.1 * g.left.2) * φ g.right.1 (h.left.1 * h.left.2)
        calc
          _ = (g.left.1 * g.left.2) *
              ((action φ g.right h.left).1 * (action φ g.right h.left).2) := by
            ac_rfl
          _ = _ := by rw [action_product]
      · rfl
    · rfl

theorem projection_surjective : Function.Surjective (projection φ) := by
  rintro ⟨q, c⟩
  refine ⟨⟨(q.left, 1), (q.right, c)⟩, ?_⟩
  apply Prod.ext
  · apply SemidirectProduct.ext
    · exact mul_one _
    · rfl
  · rfl

theorem mem_projection_ker (g : Model φ) :
    g ∈ (projection φ).ker ↔ g.left.1 * g.left.2 = 1 ∧ g.right = 1 := by
  constructor
  · intro hg
    have h := MonoidHom.mem_ker.mp hg
    have hleft := congrArg (fun z : Local φ × Binary ↦ z.1.left) h
    have hright := congrArg (fun z : Local φ × Binary ↦ z.1.right) h
    have hbinary := congrArg (fun z : Local φ × Binary ↦ z.2) h
    exact ⟨hleft, Prod.ext hright hbinary⟩
  · rintro ⟨hv, hr⟩
    apply MonoidHom.mem_ker.mpr
    apply Prod.ext
    · apply SemidirectProduct.ext hv (congrArg (fun h : R × Binary ↦ h.1) hr)
    · exact congrArg (fun h : R × Binary ↦ h.2) hr

def translations : Subgroup (Model φ) := (inl : V × V →* Model φ).range

instance translations_normal : (translations φ).Normal := by
  rw [translations, range_inl_eq_ker_rightHom]
  infer_instance

theorem selfCentralizing [Nontrivial V] (hφ : Function.Injective φ)
    (g : Model φ) (hg : ∀ v ∈ translations φ, g * v = v * g) :
    g ∈ translations φ := by
  have hc : g ∈ Subgroup.centralizer (translations φ : Set (Model φ)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (hg v hv).symm
  have ha : action φ g.right = 1 :=
    (SemidirectAbelianCentralizer.mem_centralizer_iff (action φ) g).mp hc
  have hr : g.right = 1 :=
    action_injective φ hφ (ha.trans (action φ).map_one.symm)
  rw [translations, range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
  exact hr

theorem conj_inl (g : Model φ) (v : V × V) :
    g * inl v * g⁻¹ = inl (action φ g.right v) := by
  conv_lhs => rw [← inl_left_mul_inr_right g]
  have h : (inr g.right : Model φ) * inl v * (inr g.right)⁻¹ =
      inl (action φ g.right v) := by
    rw [← map_inv]
    exact (inl_aut (φ := action φ) g.right v).symm
  calc
    (inl g.left * inr g.right : Model φ) * inl v * (inl g.left * inr g.right)⁻¹ =
        inl g.left * ((inr g.right : Model φ) * inl v * (inr g.right)⁻¹) *
          (inl g.left)⁻¹ := by group
    _ = inl (g.left * action φ g.right v * g.left⁻¹) := by
      rw [h, ← map_inv, ← map_mul, ← map_mul]
    _ = _ := by rw [mul_comm g.left, mul_inv_cancel_right]

end BinaryDiagonalSwap
end SymmetricSubgroupAsymptotics

end
