import SymmetricSubgroupAsymptotics.NonabelianChiefOrderSaving
import Mathlib.GroupTheory.Subgroup.Simple

/-! A nonabelian simple quotient forces a nonabelian interval in every
actual chief series. Its full order is saved from the abelian charge.
Central abelian kernels are permitted. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics

variable {G S : Type} [Group G] [Finite G] [Group S] [Finite S]

theorem actualChiefSeriesAbelianLength_add_surjective_interval_order_le
    (s : ActualChiefSeries G) (j : Fin s.length)
    (f : normalChainQuotient (s.subgroup j.castSucc) (s.subgroup j.succ) →* S)
    (hf : Function.Surjective f) (hnc : ¬ IsMulCommutative S) :
    actualChiefSeriesAbelianLength s + ArithmeticFunction.cardFactors (Nat.card S) ≤
      ArithmeticFunction.cardFactors (Nat.card G) := by
  let Q := normalChainQuotient (s.subgroup j.castSucc) (s.subgroup j.succ)
  have hQ : ¬ IsMulCommutative Q := by
    intro h
    letI := h
    apply hnc
    refine ⟨⟨?_⟩⟩
    intro x y
    obtain ⟨a,rfl⟩ := hf x
    obtain ⟨b,rfl⟩ := hf y
    rw [← map_mul, ← map_mul, mul_comm a b]
  have hdiv : Nat.card S ∣ Nat.card Q := Subgroup.card_dvd_of_surjective f hf
  obtain ⟨c,hc⟩ := hdiv
  have hc0 : c ≠ 0 := by
    intro h
    have hz : Nat.card Q = 0 := by simpa [h] using hc
    exact (Nat.card_pos (α := Q)).ne' hz
  have hcard : ArithmeticFunction.cardFactors (Nat.card S) ≤
      ArithmeticFunction.cardFactors (Nat.card Q) := by
    rw [hc, ArithmeticFunction.cardFactors_mul (Nat.card_pos (α := S)).ne' hc0]
    omega
  exact (Nat.add_le_add_left hcard _).trans
    (actualChiefSeriesAbelianLength_add_nonabelian_order_le s j hQ)

theorem actualChiefSeriesAbelianLength_add_simple_quotient_order_le
    [IsSimpleGroup S] (s : ActualChiefSeries G)
    (f : G →* S) (hf : Function.Surjective f)
    (hnc : ¬ IsMulCommutative S) :
    actualChiefSeriesAbelianLength s + ArithmeticFunction.cardFactors (Nat.card S) ≤
      ArithmeticFunction.cardFactors (Nat.card G) := by
  let image (i : Fin (s.length+1)) := (s.subgroup i).map f
  have hn (i : Fin (s.length+1)) : (image i).Normal := (s.normal i).map f hf
  have hi (i : Fin (s.length+1)) : image i=⊥ ∨ image i=⊤ :=
    IsSimpleGroup.eq_bot_or_eq_top_of_normal _ (hn i)
  have h0 : image 0=⊥ := by simp [image,s.head]
  have hl : image (Fin.last s.length)=⊤ := by
    change (s.subgroup (Fin.last s.length)).map f = ⊤
    rw [s.last]
    apply top_unique
    intro y _
    obtain ⟨x,rfl⟩ := hf y
    exact ⟨x,by trivial,rfl⟩
  have hm : Monotone image := by
    intro i j hij
    exact Subgroup.map_mono ((Fin.strictMono_iff_lt_succ.mpr s.step).monotone hij)
  have hex : ∃ j : Fin s.length, image j.castSucc ≠ image j.succ := by
    by_contra h
    push Not at h
    have hall : ∀ i : Fin (s.length+1), image i=image 0 := by
      intro i
      induction i using Fin.induction with
      | zero => rfl
      | succ i ih => exact (h i).symm.trans ih
    have hbad : (⊤ : Subgroup S)=⊥ := hl.symm.trans ((hall _).trans h0)
    exact top_ne_bot hbad
  obtain ⟨j,hj⟩ := hex
  have hb : image j.castSucc=⊥ := by
    rcases hi j.castSucc with h | h
    · exact h
    · exact False.elim (hj (h.trans (top_le_iff.mp (by simpa only [h] using hm (Fin.castSucc_le_succ j))).symm))
  have ht : image j.succ=⊤ := by
    rcases hi j.succ with h | h
    · exact False.elim (hj (hb.trans h.symm))
    · exact h
  let B := s.subgroup j.castSucc
  let L := s.subgroup j.succ
  have hker : B ≤ f.ker := by
    intro x hx
    have hmem : f x ∈ image j.castSucc := ⟨x,hx,rfl⟩
    rw [hb] at hmem
    exact hmem
  let lifted : G ⧸ B →* S := QuotientGroup.lift B f hker
  let q : normalChainQuotient B L →* S :=
    lifted.comp (normalChainQuotient B L).subtype
  have hq : Function.Surjective q := by
    intro y
    have hy : y ∈ image j.succ := by rw [ht]; trivial
    obtain ⟨x,hx,rfl⟩ := hy
    exact ⟨normalChainMap B L ⟨x,hx⟩,rfl⟩
  exact actualChiefSeriesAbelianLength_add_surjective_interval_order_le s j q hq hnc

end SymmetricSubgroupAsymptotics
