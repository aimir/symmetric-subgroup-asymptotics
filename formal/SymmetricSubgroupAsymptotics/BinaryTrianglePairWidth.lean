import SymmetricSubgroupAsymptotics.BinaryThreeVariablePairMonomialWidth
import SymmetricSubgroupAsymptotics.BinaryBooleanFourSupportRelabel
import SymmetricSubgroupAsymptotics.BinaryGenericPairLeadingGeneratorBound

/-! A singleton shear and the quadratic triangle on its complementary
variables give two-layer width six. Only abstract leading labels are
reindexed; the original point coordinates and vectors are retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryTrianglePairWidth
open BinaryElementaryPairMonomialWidth

def Allowed (i : Fin 4) (s : Finset (Fin 4)) : Prop :=
  (i ∉ s ∧ s.card ≤ 2) ∨ s = {i}

private theorem allowed_map_iff (p : Equiv.Perm (Fin 4)) (i : Fin 4) (hi : p i = 0)
    (s : Finset (Fin 4)) :
    BinaryThreeVariablePairMonomialWidth.Allowed (s.map p.toEmbedding) ↔ Allowed i s := by
  have hm : 0 ∈ s.map p.toEmbedding ↔ i ∈ s := by
    constructor
    · intro h
      obtain ⟨j, hj, he⟩ := Finset.mem_map.mp h
      have he' : j = i := p.injective (he.trans hi.symm)
      exact he' ▸ hj
    · intro h
      exact Finset.mem_map.mpr ⟨i, h, hi⟩
  have hs : ({i} : Finset (Fin 4)).map p.toEmbedding = {0} := by
    rw [Finset.map_singleton]
    change {p i} = {0}
    rw [hi]
  simp only [BinaryThreeVariablePairMonomialWidth.Allowed, Allowed, hm, Finset.card_map,
    ← hs]
  simp only [Finset.map_inj]

private theorem raises_relabel_iff (p : Equiv.Perm (Fin 4)) (i : Fin 4) (hi : p i = 0)
    (a b : Monomial) :
    BinaryThreeVariablePairMonomialWidth.Raises
      (BinaryBooleanFourSupportRelabel.monomial p a) (BinaryBooleanFourSupportRelabel.monomial p b) ↔
    BinaryGenericPairLeadingGeneratorBound.Raises (Allowed i) a b := by
  rcases a with ⟨l, a⟩
  rcases b with ⟨r, b⟩
  cases l <;> cases r <;>
    simp only [BinaryBooleanFourSupportRelabel.monomial_apply,
      BinaryThreeVariablePairMonomialWidth.Raises, BinaryGenericPairLeadingGeneratorBound.Raises,
      Bool.false_eq_true, Bool.true_eq_false, if_false, if_true,
      BinaryBooleanFourSupportRelabel.support_mask, Finset.map_subset_map, false_and, true_and]
  rw [← Finset.map_sdiff]
  exact allowed_map_iff p i hi _

theorem antichain_card_le_six (i : Fin 4) (s : Finset Monomial)
    (hs : IsAntichain (BinaryGenericPairLeadingGeneratorBound.Raises (Allowed i)) (s : Set Monomial)) :
    s.card ≤ 6 := by
  classical
  let p := Equiv.swap i (0 : Fin 4)
  have hi : p i = 0 := Equiv.swap_apply_left _ _
  let e := BinaryBooleanFourSupportRelabel.monomial p
  have ht : IsAntichain BinaryThreeVariablePairMonomialWidth.Raises
      (s.map e.toEmbedding : Set Monomial) := by
    intro a ha b hb hne hab
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hb
    exact hs hx hy (fun he => hne (congrArg e he)) ((raises_relabel_iff p i hi x y).mp hab)
  have hb := BinaryThreeVariablePairMonomialWidth.antichain_card_le_six _ ht
  simpa only [Finset.card_map] using hb

end SymmetricSubgroupAsymptotics.BinaryTrianglePairWidth
