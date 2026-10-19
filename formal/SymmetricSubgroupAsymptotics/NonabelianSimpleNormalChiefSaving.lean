import SymmetricSubgroupAsymptotics.NonabelianSimpleQuotientChiefSaving

/-! A nonabelian simple normal subgroup injects into one interval of every
actual chief series. Its full order is saved, without uniqueness of a
minimal normal subgroup. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics

variable {G S : Type} [Group G] [Finite G] [Group S] [Finite S]

theorem actualChiefSeriesAbelianLength_add_injective_interval_order_le
    (s : ActualChiefSeries G) (j : Fin s.length)
    (f : S →* normalChainQuotient (s.subgroup j.castSucc) (s.subgroup j.succ))
    (hf : Function.Injective f) (hnc : ¬ IsMulCommutative S) :
    actualChiefSeriesAbelianLength s + ArithmeticFunction.cardFactors (Nat.card S) ≤
      ArithmeticFunction.cardFactors (Nat.card G) := by
  let Q := normalChainQuotient (s.subgroup j.castSucc) (s.subgroup j.succ)
  have hQ : ¬ IsMulCommutative Q := by
    intro h
    letI := h
    apply hnc
    refine ⟨⟨?_⟩⟩
    intro x y
    apply hf
    rw [map_mul,map_mul,mul_comm (f x) (f y)]
  obtain ⟨c,hc⟩ := Subgroup.card_dvd_of_injective f hf
  have hc0 : c ≠ 0 := by
    intro h
    have hz : Nat.card Q=0 := by simpa [h] using hc
    exact (Nat.card_pos (α := Q)).ne' hz
  have hcard : ArithmeticFunction.cardFactors (Nat.card S) ≤
      ArithmeticFunction.cardFactors (Nat.card Q) := by
    rw [hc,ArithmeticFunction.cardFactors_mul (Nat.card_pos (α := S)).ne' hc0]
    omega
  exact (Nat.add_le_add_left hcard _).trans
    (actualChiefSeriesAbelianLength_add_nonabelian_order_le s j hQ)

theorem actualChiefSeriesAbelianLength_add_simple_normal_order_le
    (E : Subgroup G) [E.Normal] [IsSimpleGroup E]
    (s : ActualChiefSeries G) (hnc : ¬ IsMulCommutative E) :
    actualChiefSeriesAbelianLength s + ArithmeticFunction.cardFactors (Nat.card E) ≤
      ArithmeticFunction.cardFactors (Nat.card G) := by
  let cut (i : Fin (s.length+1)) : Subgroup E := (s.subgroup i).comap E.subtype
  have hn (i : Fin (s.length+1)) : (cut i).Normal := (s.normal i).comap E.subtype
  have hi (i : Fin (s.length+1)) : cut i=⊥ ∨ cut i=⊤ :=
    IsSimpleGroup.eq_bot_or_eq_top_of_normal _ (hn i)
  have h0 : cut 0=⊥ := by
    ext x
    simp [cut,s.head]
  have hl : cut (Fin.last s.length)=⊤ := by simp [cut,s.last]
  have hm : Monotone cut := by
    intro i j hij
    exact Subgroup.comap_mono ((Fin.strictMono_iff_lt_succ.mpr s.step).monotone hij)
  have hex : ∃ j : Fin s.length,cut j.castSucc ≠ cut j.succ := by
    by_contra h
    push Not at h
    have hall : ∀ i : Fin (s.length+1),cut i=cut 0 := by
      intro i
      induction i using Fin.induction with
      | zero => rfl
      | succ i ih => exact (h i).symm.trans ih
    have hbad : (⊤ : Subgroup E)=⊥ := hl.symm.trans ((hall _).trans h0)
    exact top_ne_bot hbad
  obtain ⟨j,hj⟩ := hex
  have hb : cut j.castSucc=⊥ := by
    rcases hi j.castSucc with h | h
    · exact h
    · exact False.elim (hj (h.trans (top_le_iff.mp
        (by simpa only [h] using hm (Fin.castSucc_le_succ j))).symm))
  have ht : cut j.succ=⊤ := by
    rcases hi j.succ with h | h
    · exact False.elim (hj (hb.trans h.symm))
    · exact h
  let B := s.subgroup j.castSucc
  let L := s.subgroup j.succ
  have hEL : E ≤ L := by
    intro x hx
    have hm : (⟨x,hx⟩ : E) ∈ cut j.succ := by rw [ht]; trivial
    exact hm
  let f : E →* normalChainQuotient B L :=
    (normalChainMap B L).comp (Subgroup.inclusion hEL)
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hm : (x : G) ∈ B := (QuotientGroup.eq_one_iff _).mp
      (congrArg (fun z : normalChainQuotient B L => z.val) hx)
    have hmE : x ∈ cut j.castSucc := hm
    rw [hb] at hmE
    exact hmE
  exact actualChiefSeriesAbelianLength_add_injective_interval_order_le s j f hf hnc

end SymmetricSubgroupAsymptotics
