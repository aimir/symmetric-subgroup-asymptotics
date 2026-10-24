import SymmetricSubgroupAsymptotics.SubnormalElementaryAbelianIrreducible
import SymmetricSubgroupAsymptotics.SemidirectSubgroupContainingLeft
import Mathlib.Tactic.Group

/-! Bind the actual right image of a subnormal subgroup of an abelian
semidirect product to conjugation on the same original translations.
Irreducibility is about that inherited action, not an abstract module
chosen after changing the subgroup. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.SubnormalSemidirectTranslation
open SemidirectProduct IrreducibleAbelianSemidirect
open SubnormalElementaryAbelianIrreducible

section Action
variable {V H : Type} [CommGroup V] [Group H] (φ : H →* MulAut V)

theorem conjugate_inl (g : V ⋊[φ] H) (v : V) :
    g * inl v * g⁻¹ = inl (φ g.right v) := by
  have hc : (inl g.left : V ⋊[φ] H) * inl (φ g.right v) =
      inl (φ g.right v) * inl g.left := by
    rw [← map_mul,← map_mul,mul_comm]
  calc
    g * inl v * g⁻¹ =
        inl g.left * (inr g.right * inl v * (inr g.right)⁻¹) *
          (inl g.left)⁻¹ :=
      (congrArg (fun q : V ⋊[φ] H => q * inl v * q⁻¹)
        (inl_left_mul_inr_right g).symm).trans (by group)
    _ = inl g.left * inl (φ g.right v) * (inl g.left)⁻¹ := by
      rw [← map_inv,← inl_aut]
    _ = inl (φ g.right v) := by
      rw [hc,mul_assoc,mul_inv_cancel,mul_one]

theorem irreducible_conjugation_translations (N : Subgroup (V ⋊[φ] H))
    (hirr : Irreducible
      (φ.comp (N.map (rightHom : V ⋊[φ] H →* H)).subtype)) :
    IrreducibleConjugation N (translations φ) := by
  intro W hWT hNW
  let S := W.comap (inl : V →* V ⋊[φ] H)
  have hstable : ∀ e : N.map (rightHom : V ⋊[φ] H →* H),
      ∀ v ∈ S, φ e.val v ∈ S := by
    intro e v hv
    obtain ⟨g,hg,he⟩ := e.property
    have hn : g ∈ Subgroup.normalizer (W : Set (V ⋊[φ] H)) := hNW hg
    have hw : g * inl v * g⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp hn (inl v)).mp hv
    rw [conjugate_inl φ g v] at hw
    change g.right = e.val at he
    change inl (φ e.val v) ∈ W
    simpa only [he] using hw
  rcases hirr S hstable with hzero | hfull
  · left
    apply le_antisymm ?_ bot_le
    intro w hw
    obtain ⟨v,hv⟩ := hWT hw
    have hvS : v ∈ S := by
      change inl v ∈ W
      rw [hv]
      exact hw
    have hv1 : v = 1 := Subgroup.mem_bot.mp (hzero ▸ hvS)
    exact Subgroup.mem_bot.mpr (hv.symm.trans (by rw [hv1,map_one]))
  · right
    apply le_antisymm hWT
    rintro w ⟨v,rfl⟩
    have hvS : v ∈ S := by rw [hfull]; exact Subgroup.mem_top v
    exact hvS

theorem contains_translations (hφ : Function.Injective φ)
    (N : Subgroup (V ⋊[φ] H)) (hN : N.IsSubnormal)
    (hne : N.map (rightHom : V ⋊[φ] H →* H) ≠ ⊥)
    (hirr : Irreducible
      (φ.comp (N.map (rightHom : V ⋊[φ] H →* H)).subtype)) :
    translations φ ≤ N := by
  apply le_of_subnormal_irreducible_noncentral (translations φ) N hN
    (irreducible_conjugation_translations φ N hirr)
  intro hcentral
  apply hne
  apply le_antisymm ?_ bot_le
  rintro e ⟨g,hg,rfl⟩
  have ha : φ g.right = 1 :=
    (SemidirectAbelianCentralizer.mem_centralizer_iff φ g).mp (hcentral hg)
  exact Subgroup.mem_bot.mpr (hφ (ha.trans φ.map_one.symm))

end Action

theorem genRank_le_image_add_one
    {V H : Type} [CommGroup V] [Finite V] [Nontrivial V] [Group H] [Finite H]
    (φ : H →* MulAut V) (hφ : Function.Injective φ)
    (N : Subgroup (V ⋊[φ] H)) (hN : N.IsSubnormal)
    (hne : N.map (rightHom : V ⋊[φ] H →* H) ≠ ⊥)
    (hirr : Irreducible
      (φ.comp (N.map (rightHom : V ⋊[φ] H →* H)).subtype)) :
    MarkedC4.genRank N ≤ MarkedC4.genRank (N.map (rightHom : V ⋊[φ] H →* H))+1 :=
  SemidirectSubgroupContainingLeft.genRank_le_image_add_one φ N
    (contains_translations φ hφ N hN hne hirr) hirr

end SymmetricSubgroupAsymptotics.SubnormalSemidirectTranslation
