import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Order.Atoms

/-! The original left coset action attached to an actual rank-one
two-cell cover. All coordinates live in the given group and subgroup;
no independent permutation representation is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGRankOneCosetAction

variable {G : Type*} [Group G] (B U : Subgroup G) (w : G)

theorem isCoatom (hUB : U ≤ B) (hw : w ∉ B)
    (hcover : ∀ g : G, g ∈ B ∨ ∃ (b : B) (u : U), g = b.val*w*u.val) :
    IsCoatom B := by
  refine SetLike.isCoatom_iff.mpr ⟨?_, ?_⟩
  · intro he
    apply hw
    rw [he]
    exact Subgroup.mem_top w
  · intro H g hBH hg hHg
    obtain ⟨b,u,he⟩ := (hcover g).resolve_left hg
    have hwH : w ∈ H := by
      have hh := H.mul_mem (H.mul_mem (H.inv_mem (hBH b.property)) hHg)
        (H.inv_mem (hBH (hUB u.property)))
      rw [he] at hh
      simpa [mul_assoc] using hh
    apply top_unique
    intro x _
    rcases hcover x with hx | ⟨c,v,rfl⟩
    · exact hBH hx
    · exact H.mul_mem (H.mul_mem (hBH c.property) hwH) (hBH (hUB v.property))

/-- Every ordered pair of distinct original cosets is reached from the
original base pair (B,wB). -/
theorem exists_pair_transport
    (hcover : ∀ g : G, g ∈ B ∨ ∃ (b : B) (u : U), g = b.val*w*u.val)
    (hUB : U ≤ B) {a b : G ⧸ B} (hab : a ≠ b) :
    ∃ g : G, g • ((1 : G) : G ⧸ B) = a ∧ g • (w : G ⧸ B) = b := by
  induction a using Quotient.inductionOn' with
  | h a =>
    induction b using Quotient.inductionOn' with
    | h b =>
      have hn : a⁻¹*b ∉ B := fun h => hab (QuotientGroup.eq.mpr h)
      obtain ⟨c,u,he⟩ := (hcover (a⁻¹*b)).resolve_left hn
      have hb : b = a*c.val*w*u.val := by
        have hh := congrArg (fun z : G => a*z) he
        simpa only [mul_assoc, mul_inv_cancel_left] using hh
      refine ⟨a*c.val, ?_, ?_⟩
      · change (((a*c.val)*1 : G) : G ⧸ B) = (a : G ⧸ B)
        apply QuotientGroup.eq.mpr
        simp [mul_assoc]
      · change (((a*c.val)*w : G) : G ⧸ B) = (b : G ⧸ B)
        apply QuotientGroup.eq.mpr
        rw [hb]
        simpa [mul_assoc] using hUB u.property

theorem isMultiplyPretransitive_two (hUB : U ≤ B)
    (hcover : ∀ g : G, g ∈ B ∨ ∃ (b : B) (u : U), g = b.val*w*u.val) :
    MulAction.IsMultiplyPretransitive G (G ⧸ B) 2 := by
  apply MulAction.is_two_pretransitive_iff.mpr
  intro a b c d hab hcd
  obtain ⟨g,hga,hgb⟩ := exists_pair_transport B U w hcover hUB hab
  obtain ⟨h,hgc,hgd⟩ := exists_pair_transport B U w hcover hUB hcd
  refine ⟨h*g⁻¹, ?_, ?_⟩
  · rw [mul_smul, ←hga, inv_smul_smul, hgc]
  · rw [mul_smul, ←hgb, inv_smul_smul, hgd]

theorem isPreprimitive (hUB : U ≤ B)
    (hcover : ∀ g : G, g ∈ B ∨ ∃ (b : B) (u : U), g = b.val*w*u.val) :
    MulAction.IsPreprimitive G (G ⧸ B) :=
  MulAction.isPreprimitive_of_is_two_pretransitive
    (isMultiplyPretransitive_two B U w hUB hcover)

end SymmetricSubgroupAsymptotics.CFSGRankOneCosetAction
