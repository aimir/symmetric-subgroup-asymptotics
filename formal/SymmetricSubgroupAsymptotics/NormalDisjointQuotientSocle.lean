import SymmetricSubgroupAsymptotics.ZmudFaithfulCharacterInput
import Mathlib.Order.Preorder.Finite
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Make an original normal section essential by killing a maximal normal
subgroup disjoint from it. In the resulting actual quotient, every minimal
normal subgroup lies in the retained image. Applied to a central elementary
section, whose image already lies in the socle, this identifies the entire
socle without a classification or a normal-generator monotonicity claim. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.NormalDisjointQuotientSocle

variable {G : Type} [Group G] [Finite G] (A : Subgroup G) [A.Normal]

theorem exists_maximal_disjoint_normal :
    ∃ B : Subgroup G, B.Normal ∧ Disjoint A B ∧
      ∀ K : Subgroup G, K.Normal → Disjoint A K → B ≤ K → K ≤ B := by
  let s : Set (Subgroup G) := {B | B.Normal ∧ Disjoint A B}
  obtain ⟨B, hB, hmax⟩ := s.toFinite.exists_maximal
    (show s.Nonempty from ⟨⊥, inferInstance, disjoint_bot_right⟩)
  exact ⟨B, hB.1, hB.2, fun K hK hd hBK => hmax ⟨hK, hd⟩ hBK⟩

variable (B : Subgroup G) [B.Normal]
  (hdisjoint : Disjoint A B)
  (hmax : ∀ K : Subgroup G, K.Normal → Disjoint A K → B ≤ K → K ≤ B)

include hdisjoint hmax in
/-- Every nonzero normal subgroup of the literal quotient meets the
unchanged image of the retained original subgroup. -/
theorem image_meets_normal (M : Subgroup (G ⧸ B)) [M.Normal] (hM : M ≠ ⊥) :
    M ⊓ A.map (QuotientGroup.mk' B) ≠ ⊥ := by
  intro hinter
  let q : G →* G ⧸ B := QuotientGroup.mk' B
  let K : Subgroup G := M.comap q
  letI : K.Normal := Subgroup.Normal.comap inferInstance q
  have hBK : B ≤ K := QuotientGroup.le_comap_mk' B M
  have hdAK : Disjoint A K := by
    apply disjoint_iff_inf_le.mpr
    intro a ha
    have hqa : q a ∈ M ⊓ A.map q := ⟨ha.2, ⟨a, ha.1, rfl⟩⟩
    have hqaone : q a = 1 := Subgroup.mem_bot.mp (hinter ▸ hqa)
    have haB : a ∈ B := (QuotientGroup.eq_one_iff (N := B) a).mp hqaone
    exact (disjoint_iff_inf_le.mp hdisjoint) ⟨ha.1, haB⟩
  have hKB : K ≤ B := hmax K inferInstance hdAK hBK
  apply hM
  apply le_antisymm _ bot_le
  intro y hy
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective B y
  exact (QuotientGroup.eq_one_iff (N := B) g).mpr (hKB hy)

include hdisjoint hmax in
/-- The actual quotient socle is inside the retained image. Central
prime-exponent images supply the reverse inclusion separately. -/
theorem socle_le_image :
    finiteGroupSocle (G ⧸ B) ≤ A.map (QuotientGroup.mk' B) := by
  letI : (A.map (QuotientGroup.mk' B)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective B)
  rw [finiteGroupSocle]
  apply Subgroup.normalClosure_le_normal
  rintro x ⟨M, hM, hx⟩
  letI : M.Normal := hM.1
  have hi : M ⊓ A.map (QuotientGroup.mk' B) = M :=
    hM.2.2 _ inferInstance (image_meets_normal A B hdisjoint hmax M hM.2.1) inf_le_left
  exact (show M ≤ A.map (QuotientGroup.mk' B) by rw [← hi]; exact inf_le_right) hx

include hdisjoint in
/-- Restriction of the original quotient map is injective on the retained
section; its cardinal and module rank are therefore not diminished. -/
theorem quotientMap_injective_on :
    Function.Injective ((QuotientGroup.mk' B).comp A.subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro a ha
  have haB : (a : G) ∈ B := (QuotientGroup.eq_one_iff (N := B) (a : G)).mp ha
  apply Subtype.ext
  exact Subgroup.mem_bot.mp ((disjoint_iff_inf_le.mp hdisjoint) ⟨a.2, haB⟩)

end SymmetricSubgroupAsymptotics.NormalDisjointQuotientSocle

end
