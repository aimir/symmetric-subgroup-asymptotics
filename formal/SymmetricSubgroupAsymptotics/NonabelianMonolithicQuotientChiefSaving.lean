import SymmetricSubgroupAsymptotics.NonabelianSimpleNormalChiefSaving

/-! A quotient with a nonabelian normal subgroup contained in every
nontrivial normal subgroup saves that subgroup's full order in every
actual chief series of the original group. No uniqueness condition is
imposed on the original group. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics

variable {G S : Type} [Group G] [Finite G] [Group S] [Finite S]

theorem actualChiefSeriesAbelianLength_add_monolithic_quotient_order_le
    (s : ActualChiefSeries G) (f : G →* S) (hf : Function.Surjective f)
    (E : Subgroup S) [E.Normal] (hnc : ¬ IsMulCommutative E)
    (hcore : ∀ K : Subgroup S, K.Normal → K ≠ ⊥ → E ≤ K) :
    actualChiefSeriesAbelianLength s + ArithmeticFunction.cardFactors (Nat.card E) ≤
      ArithmeticFunction.cardFactors (Nat.card G) := by
  let image (i : Fin (s.length+1)) := (s.subgroup i).map f
  have hn (i : Fin (s.length+1)) : (image i).Normal := (s.normal i).map f hf
  have h0 : image 0=⊥ := by simp [image,s.head]
  have hl : image (Fin.last s.length)=⊤ := by
    change (s.subgroup (Fin.last s.length)).map f=⊤
    rw [s.last]
    apply top_unique
    intro y _
    obtain ⟨x,rfl⟩ := hf y
    exact ⟨x,by trivial,rfl⟩
  have htop : (⊤ : Subgroup S) ≠ ⊥ := by
    intro h
    apply hnc
    refine ⟨⟨?_⟩⟩
    have he (z : E) : z=1 := by
      apply Subtype.ext
      have hz : (z : S) ∈ (⊤ : Subgroup S) := by trivial
      rw [h] at hz
      exact hz
    intro x y
    rw [he x,he y]
  have hex : ∃ j : Fin s.length,image j.castSucc=⊥ ∧ image j.succ ≠ ⊥ := by
    by_contra h
    push Not at h
    have hall : ∀ i : Fin (s.length+1),image i=⊥ := by
      intro i
      induction i using Fin.induction with
      | zero => exact h0
      | succ i ih => exact h i ih
    exact htop (hl.symm.trans (hall _))
  obtain ⟨j,hb,ht⟩ := hex
  let B := s.subgroup j.castSucc
  let L := s.subgroup j.succ
  let I : Subgroup S := image j.succ
  have hEI : E ≤ I := hcore I (hn j.succ) ht
  have hker : B ≤ f.ker := by
    intro x hx
    have hm : f x ∈ image j.castSucc := ⟨x,hx,rfl⟩
    rw [hb] at hm
    exact hm
  let lifted : G ⧸ B →* S := QuotientGroup.lift B f hker
  let qbase : normalChainQuotient B L →* S :=
    lifted.comp (normalChainQuotient B L).subtype
  have hmem (x : normalChainQuotient B L) : qbase x ∈ I := by
    rcases x with ⟨x,a,ha,rfl⟩
    exact ⟨a,ha,rfl⟩
  let q : normalChainQuotient B L →* I := qbase.codRestrict I hmem
  have hq : Function.Surjective q := by
    rintro ⟨y,a,ha,rfl⟩
    exact ⟨normalChainMap B L ⟨a,ha⟩,rfl⟩
  have hI : ¬ IsMulCommutative I := by
    intro h
    letI := h
    apply hnc
    refine ⟨⟨?_⟩⟩
    intro x y
    apply (Subgroup.inclusion_injective hEI)
    rw [map_mul,map_mul,mul_comm]
  obtain ⟨c,hc⟩ := Subgroup.card_dvd_of_injective
    (Subgroup.inclusion hEI) (Subgroup.inclusion_injective hEI)
  have hc0 : c ≠ 0 := by
    intro h
    have hz : Nat.card I=0 := by simpa [h] using hc
    exact (Nat.card_pos (α := I)).ne' hz
  have hcard : ArithmeticFunction.cardFactors (Nat.card E) ≤
      ArithmeticFunction.cardFactors (Nat.card I) := by
    rw [hc,ArithmeticFunction.cardFactors_mul (Nat.card_pos (α := E)).ne' hc0]
    omega
  exact (Nat.add_le_add_left hcard _).trans
    (actualChiefSeriesAbelianLength_add_surjective_interval_order_le s j q hq hI)

end SymmetricSubgroupAsymptotics
