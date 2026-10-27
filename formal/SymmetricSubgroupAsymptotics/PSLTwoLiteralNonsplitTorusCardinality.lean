import SymmetricSubgroupAsymptotics.PSLTwoLiteralNonsplitNormDictionary
import SymmetricSubgroupAsymptotics.PSLTwoLiteralNonsplitQuotientNormalizer
import Mathlib.Data.Set.Card

/-! Exact central factor2 and a genuine noncentral literal torus element.
No finite-field cardinality or group-order callback is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PSLTwoLiteralNonsplitTorusCardinality
open PSLTwoLiteralNonsplitTorusCyclic PSLTwoLiteralNonsplitNormalizerStructure
open PSLTwoLiteralNonsplitQuotientNormalizer PSLTwoLiteralNonsplitNormDictionary
variable {F : Type*} [Field F]
local notation "SL2" => Matrix.SpecialLinearGroup (Fin 2) F

theorem projection_neg_one : projection (-1 : SL2)=1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
  refine ⟨(-1 : F),by norm_num,?_⟩
  ext i j
  by_cases hij : i = j <;> simp [Matrix.scalar_apply, Matrix.diagonal, Matrix.one_apply, hij]

theorem projection_eq_one_iff (A : SL2) : projection A=1 ↔ A=1 ∨ A= -1 := by
  constructor
  · intro h
    obtain ⟨r,hr,he⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp
      ((QuotientGroup.eq_one_iff _).mp h)
    have hs : r*r=1 := by simpa only [Fintype.card_fin,pow_two] using hr
    rcases mul_self_eq_one_iff.mp hs with h1|h1
    · left
      apply Subtype.ext
      rw [←he,h1]
      ext i j
      by_cases hij : i = j <;> simp [Matrix.scalar_apply, Matrix.diagonal, Matrix.one_apply, hij]
    · right
      apply Subtype.ext
      rw [←he,h1]
      ext i j
      by_cases hij : i = j <;> simp [Matrix.scalar_apply, Matrix.diagonal, Matrix.one_apply, hij]
  · rintro (rfl|rfl)
    · exact map_one projection
    · exact projection_neg_one

theorem negative_one_mem (ν : F) : (-1 : SL2) ∈ nonsplitSL ν :=
  (projection_mem_torus_iff ν (-1)).mp (by rw [projection_neg_one]; exact (nonsplitTorus ν).one_mem)

theorem neg_one_ne_one_SL (hF : ringChar F ≠ 2) : (-1 : SL2) ≠ 1 := by
  intro h
  have he := congrArg (fun A : SL2 => A.val 0 0) h
  have hv : (-1 : F)=1 := by simpa using he
  exact Ring.neg_one_ne_one_of_char_ne_two hF hv

theorem twice_torus_card [Finite F] (hF : ringChar F ≠ 2) (ν : F) (hν : ¬IsSquare ν) :
    Nat.card (nonsplitTorus ν)*2=Nat.card F+1 := by
  let H := nonsplitSL ν
  let f := (projection (F:=F)).comp H.subtype
  have hr : f.range=nonsplitTorus ν := by
    rw [MonoidHom.range_comp,Subgroup.range_subtype]
    rfl
  have hk : Nat.card f.ker=2 := by
    have hneg : (⟨-1,negative_one_mem ν⟩ : H) ∈ f.ker := projection_neg_one
    rw [Nat.card_eq_two_iff]
    refine ⟨1,⟨⟨-1,negative_one_mem ν⟩,hneg⟩,?_,?_⟩
    · intro he
      exact neg_one_ne_one_SL hF
        (congrArg (fun a : f.ker => ((a : H) : SL2)) he).symm
    · ext ⟨⟨A,hA⟩,hAk⟩
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff,Set.mem_univ,iff_true]
      have ha : projection A=1 := hAk
      rcases (projection_eq_one_iff A).mp ha with rfl|rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
  have hm := f.ker.card_mul_index
  rw [Subgroup.index_ker,hr,hk] at hm
  have hc : Nat.card H=Nat.card F+1 := card_nonsplitSL ν hν
  rw [hc] at hm
  simpa only [mul_comm] using hm

theorem torus_card [Finite F] (hF : ringChar F ≠ 2) (ν : F) (hν : ¬IsSquare ν) :
    Nat.card (nonsplitTorus ν)=(Nat.card F+1)/2 := by
  have hh := twice_torus_card hF ν hν
  omega

theorem torus_card_gcd [Fintype F] (hF : ringChar F ≠ 2) (ν : F) (hν : ¬IsSquare ν) :
    Nat.card (nonsplitTorus ν)=(Nat.card F+1)/Nat.gcd (Nat.card F-1) 2 := by
  have ho : Nat.card F % 2=1 := by
    simpa only [Nat.card_eq_fintype_card] using FiniteField.odd_card_of_char_ne_two hF
  have hd : 2 ∣ Nat.card F-1 := Nat.dvd_iff_mod_eq_zero.mpr (by omega)
  rw [Nat.gcd_eq_right hd]
  exact torus_card hF ν hν

/-- This is the missing genuine matrix witness used by the structural
normalizer theorem, constructed from the actual norm-kernel cardinality. -/
theorem exists_noncentral_SL [Finite F] (ν : F) (hν : ¬IsSquare ν) (hq : 5 ≤ Nat.card F) :
    ∃ C : SL2,C ∈ nonsplitSL ν ∧ C.val 1 0 ≠ 0 := by
  by_contra hn
  have hz (C : SL2) (hC : C ∈ nonsplitSL ν) : C.val 1 0=0 := by
    by_contra hh
    exact hn ⟨C,hC,hh⟩
  have hsub : (nonsplitSL ν : Set SL2) ⊆ ({1,-1} : Set SL2) := by
    intro C hC
    obtain ⟨h11,h01⟩ := hC
    have h10 := hz C ⟨h11,h01⟩
    have hd := det_entries C
    simp only [h11,h01,h10,mul_zero,sub_zero] at hd
    have hc : C=1 ∨ C= -1 := by
      rcases mul_self_eq_one_iff.mp hd with he|he
      · left
        apply SL_ext <;> simp [h11,h01,h10,he]
      · right
        apply SL_ext <;> simp [h11,h01,h10,he]
    exact hc
  have hb : Nat.card (nonsplitSL ν) ≤ 2 := by
    change (nonsplitSL ν : Set SL2).ncard ≤ 2
    have hp := Set.ncard_insert_le (1 : SL2) ({-1} : Set SL2)
    simp only [Set.ncard_singleton] at hp
    exact (Set.ncard_le_ncard hsub).trans hp
  rw [card_nonsplitSL ν hν] at hb
  omega

end SymmetricSubgroupAsymptotics.PSLTwoLiteralNonsplitTorusCardinality
