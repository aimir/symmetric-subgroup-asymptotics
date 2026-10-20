import SymmetricSubgroupAsymptotics.PairedFormSwapComplement
import SymmetricSubgroupAsymptotics.TwoBlockProjectionIrreducibility

/-! The actual translation action of a pairing graph and a block swap.
The complement bound and a displayed Singer projection give the affine
normal-generator bound, without converting the translation pair to a
different coordinate type. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PairedFormSwapAffine

open SemidirectProduct

variable {V R Y : Type} [CommGroup V] [Group R]
variable (φ : R →* MulAut V) (B : V → V → Y)

def localAction : R →* Equiv.Perm V where
  toFun r := (φ r).toEquiv
  map_one' := by rw [map_one]; rfl
  map_mul' r s := by rw [map_mul]; rfl

theorem localAction_injective (hφ : Function.Injective φ) :
    Function.Injective (localAction φ) := by
  intro r s h
  apply hφ
  apply MulEquiv.ext
  intro v
  exact congrArg (fun p : Equiv.Perm V ↦ p v) h

abbrev Graph := PairedFormSwapComplement.graph (localAction φ) B

variable (hsymm : ∀ x y, B x y = B y x)

abbrev Complement := PairedFormSwapComplement.Model (localAction φ) B hsymm

def action : Complement φ B hsymm →* MulAut (V × V) where
  toFun g := (φ g.left.val.1).prodCongr (φ g.left.val.2) * C2Wreath.swapAut V g.right
  map_one' := by
    apply MulEquiv.ext
    intro v
    apply Prod.ext <;> simp <;> rfl
  map_mul' g h := by
    rcases g with ⟨⟨⟨a, b⟩, hab⟩, c⟩
    rcases h with ⟨⟨⟨d, e⟩, hde⟩, f⟩
    rcases C2Wreath.cases c with rfl | rfl <;>
      rcases C2Wreath.cases f with rfl | rfl
    all_goals
      apply MulEquiv.ext
      intro v
    · change (φ (a * d) v.1, φ (b * e) v.2) =
        (φ a (φ d v.1), φ b (φ e v.2))
      rw [map_mul, map_mul]
      rfl
    · change (φ (a * d) v.2, φ (b * e) v.1) =
        (φ a (φ d v.2), φ b (φ e v.1))
      rw [map_mul, map_mul]
      rfl
    · change (φ (a * e) v.2, φ (b * d) v.1) =
        (φ a (φ e v.2), φ b (φ d v.1))
      rw [map_mul, map_mul]
      rfl
    · change (φ (a * e) v.1, φ (b * d) v.2) =
        (φ a (φ e v.1), φ b (φ d v.2))
      rw [map_mul, map_mul]
      rfl

theorem action_one (g : Graph φ B) (v : V × V) :
    action φ B hsymm (⟨g, 1⟩ : Complement φ B hsymm) v =
      (φ g.val.1 v.1, φ g.val.2 v.2) := by
  simp [action]
  rfl

theorem action_swap (g : Graph φ B) (v : V × V) :
    action φ B hsymm (⟨g, C2Wreath.gen⟩ : Complement φ B hsymm) v =
      (φ g.val.1 v.2, φ g.val.2 v.1) := by
  simp [action, C2Wreath.swapAut_gen]
  rfl

theorem action_injective [Nontrivial V] (hφ : Function.Injective φ) :
    Function.Injective (action φ B hsymm) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨g, c⟩ h
  rcases C2Wreath.cases c with rfl | rfl
  · have ha : φ g.val.1 = 1 := by
      apply MulEquiv.ext
      intro v
      have he := congrArg (fun f : MulAut (V × V) ↦ (f (v, 1)).1) h
      simpa only [action_one, MulAut.one_apply] using he
    have hb : φ g.val.2 = 1 := by
      apply MulEquiv.ext
      intro v
      have he := congrArg (fun f : MulAut (V × V) ↦ (f (1, v)).2) h
      simpa only [action_one, MulAut.one_apply] using he
    apply SemidirectProduct.ext
    · apply Subtype.ext
      exact Prod.ext (hφ (ha.trans φ.map_one.symm)) (hφ (hb.trans φ.map_one.symm))
    · rfl
  · obtain ⟨v, hv⟩ := exists_ne (1 : V)
    have he := congrArg (fun f : MulAut (V × V) ↦ (f (v, 1)).1) h
    have hv1 : 1 = v := by
      simpa only [action_swap, map_one, MulAut.one_apply] using he
    exact (hv hv1.symm).elim

abbrev Model := (V × V) ⋊[action φ B hsymm] Complement φ B hsymm

theorem normal_generating_tuples [Nontrivial V]
    (hφ : Function.Injective φ)
    (hsep : ∀ u v : V, (∀ x, B x u = B x v) → u = v)
    (hsurj : Function.Surjective (PairedFormSwapComplement.first (localAction φ) B))
    (hirr : IrreducibleAbelianSemidirect.Irreducible φ)
    (s : Complement φ B hsymm)
    (hprojection : ∀ v : V × V,
      action φ B hsymm (s ^ 4) v * action φ B hsymm (s ^ 2) v *
        action φ B hsymm s v = (1, v.2))
    (hR : ∀ N : Subgroup R, N.Normal →
      ∃ x : Fin 1 → R, Subgroup.normalClosure (Set.range x) = N) :
    ∀ N : Subgroup (Model φ B hsymm), N.Normal →
      ∃ x : Fin 2 → Model φ B hsymm, Subgroup.normalClosure (Set.range x) = N := by
  let e := PairedFormSwapComplement.firstEquiv (localAction φ) B
    (localAction_injective φ hφ) hsep hsurj
  have hirrPair : IrreducibleAbelianSemidirect.Irreducible (action φ B hsymm) := by
    apply twoBlock_irreducible_of_projection φ (action φ B hsymm) hirr
      (fun r ↦ inl (e.symm r)) ?_ (inr C2Wreath.gen) ?_ s hprojection
    · intro r v
      change action φ B hsymm (⟨e.symm r, 1⟩ : Complement φ B hsymm) (v, 1) = _
      rw [action_one, map_one]
      have he : (e.symm r).val.1 = r := e.apply_symm_apply r
      rw [he]
    · intro v
      change action φ B hsymm (⟨1, C2Wreath.gen⟩ : Complement φ B hsymm) v = _
      rw [action_swap]
      change (φ 1 v.2, φ 1 v.1) = (v.2, v.1)
      rw [map_one]
      rfl
  exact IrreducibleAbelianSemidirect.normal_generating_tuples
    (action φ B hsymm) (action_injective φ B hsymm hφ) hirrPair (by decide)
    (PairedFormSwapComplement.normal_generating_tuples (localAction φ) B hsymm
      (localAction_injective φ hφ) hsep hsurj hR)

end PairedFormSwapAffine
end SymmetricSubgroupAsymptotics

end
