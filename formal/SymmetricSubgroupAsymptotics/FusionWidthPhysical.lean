import SymmetricSubgroupAsymptotics.FusionPhysicalUnion
import SymmetricSubgroupAsymptotics.FusionPhysicalCharts
import SymmetricSubgroupAsymptotics.FusionWidthContinuation

/-! Original-weight physical continuation for mixed odd/even widths.
Local bounds concern actual surviving epimorphisms on the complete source.
The original literal normal axes are summed before normalizer division. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Filter

namespace SymmetricSubgroupAsymptotics

theorem fusionWidthPhysical_bound {w : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w))) (b : ℕ)
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop) (hP : FusionOrbitNatural U P)
    (D α : {N : Subgroup U // N.Normal} → ℝ)
    (henvelope : ∀ N J, fusionSurvivingEpiCount U P N J ≤ D N*(2:ℝ)^(α N*b)) :
    (Nat.card (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)):ℝ)/
      exactBenchmark (b+w) ≤
      ∑ N : {N : Subgroup U // N.Normal},
        fusionWidthColdKernel b w (D N)
          (Nat.card (Subgroup.normalizer (U:Set (Equiv.Perm (Fin w)))):ℝ) (α N) *
          ((subgroupCount b:ℝ)/exactBenchmark b) := by
  let a : ℝ := Nat.card (Subgroup.normalizer (U:Set (Equiv.Perm (Fin w))))
  let q : ℝ := (((b+w).factorial:ℝ)/((b.factorial:ℝ)*a))/exactBenchmark (b+w)
  have ha : 0<a := by dsimp [a]; exact_mod_cast (Nat.card_pos (α :=
    Subgroup.normalizer (U:Set (Equiv.Perm (Fin w)))))
  have hq : 0≤q := by dsimp [q]; exact div_nonneg (by positivity) (exactBenchmark_pos _).le
  have hphysical := div_le_div_of_nonneg_right
    (fusionPhysical_original_weight U P hP) (exactBenchmark_pos (b+w)).le
  have hnorm :
      (Nat.card (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)):ℝ)/
        exactBenchmark (b+w) ≤ q * ∑ N : {N : Subgroup U // N.Normal},
          ∑ J : Subgroup (Equiv.Perm (Fin b)), fusionSurvivingEpiCount U P N J := by
    convert hphysical using 1
    simp only [Fintype.card_fin,Nat.cast_sum,Nat.add_comm w b]
    unfold q a fusionSurvivingEpiCount
    ring
  calc
    _ ≤ q * ∑ N : {N : Subgroup U // N.Normal},
        ∑ J : Subgroup (Equiv.Perm (Fin b)), fusionSurvivingEpiCount U P N J := hnorm
    _ = ∑ N : {N : Subgroup U // N.Normal},
        q * ∑ J : Subgroup (Equiv.Perm (Fin b)), fusionSurvivingEpiCount U P N J := by
      rw [Finset.mul_sum]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro N _
      have hsum : (∑ J : Subgroup (Equiv.Perm (Fin b)), fusionSurvivingEpiCount U P N J) ≤
          (D N*(2:ℝ)^(α N*b))*(subgroupCount b:ℝ) := by
        calc
          _ ≤ ∑ _J : Subgroup (Equiv.Perm (Fin b)), D N*(2:ℝ)^(α N*b) :=
            Finset.sum_le_sum (fun J _ => henvelope N J)
          _ = _ := by simp [subgroupCount,Nat.card_eq_fintype_card,mul_comm]
      apply (mul_le_mul_of_nonneg_left hsum hq).trans_eq
      unfold fusionWidthColdKernel fusionWidthPointingRatio q a
      have hL := ne_of_gt (exactBenchmark_pos b)
      field_simp

def fusionWidthPointEquiv (w n : ℕ) (hn : w≤n) : Fin w ⊕ Fin (n-w) ≃ Fin n :=
  finSumFinEquiv.trans (finCongr (by omega))

def FusionWidthCanonicalFamily {w n : ℕ} (U : Subgroup (Equiv.Perm (Fin w)))
    (hn : w≤n) (P : Subgroup (U × Equiv.Perm (Fin (n-w))) → Prop) :
    Set (Subgroup (Equiv.Perm (Fin n))) :=
  FusionRelabelledFamily (fusionWidthPointEquiv w n hn)
    (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P))

/-- An arbitrary complete physical chart of width `w` enters the fixed
canonical width family.  The survival predicate is evaluated on the same
deleted subgroup, so the full complementary action and all correlations are
retained. -/
theorem fusionWidthCanonicalFamily_of_chart {w n : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w))) (hn : w ≤ n)
    (H : Subgroup (Equiv.Perm (Fin n)))
    (e : Fin w ⊕ Fin (n-w) ≃ Fin n)
    (hblock : ∀ k ∈ relabelSubgroup e.symm H,
      Set.MapsTo k (Set.range (Sum.inl : Fin w → Fin w ⊕ Fin (n-w)))
        (Set.range (Sum.inl : Fin w → Fin w ⊕ Fin (n-w))))
    (hprojection : (fusionPhysicalBlockPullback (relabelSubgroup e.symm H)).map
      (MonoidHom.fst (Equiv.Perm (Fin w)) (Equiv.Perm (Fin (n-w)))) = U)
    (P : Subgroup (U × Equiv.Perm (Fin (n-w))) → Prop)
    (hP : P (fusionDeletedModel U (relabelSubgroup e.symm H))) :
    H ∈ FusionWidthCanonicalFamily U hn P := by
  have hm := fusionDeletedModel_mem_family U (relabelSubgroup e.symm H)
    hblock hprojection P hP
  have hr := fusionRelabelledFamily_of_chart
    (FusionOrbitModel U (FusionAcceptedOrbitPredicate U P))
    e (fusionWidthPointEquiv w n hn) (relabelSubgroup e.symm H) hm
  simpa only [relabelSubgroup_trans, Equiv.symm_trans_self,
    relabelSubgroup_refl] using hr

theorem fusionWidthCanonicalFamily_card {w n : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w))) (hn : w≤n)
    (P : Subgroup (U × Equiv.Perm (Fin (n-w))) → Prop) :
    Nat.card (FusionWidthCanonicalFamily U hn P)=
      Nat.card (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) :=
  fusionRelabelledFamily_card _ _

section Menu
variable {ι : Type*} [Fintype ι] (w : ι → ℕ)
variable (U : ∀ i, Subgroup (Equiv.Perm (Fin (w i))))

abbrev FusionWidthMenuAxis := Σ i, {N : Subgroup (U i) // N.Normal}

def fusionWidthMenuDivisor (i : ι) : ℝ :=
  Nat.card (Subgroup.normalizer (U i:Set (Equiv.Perm (Fin (w i)))))

omit [Fintype ι] in
theorem fusionWidthMenuDivisor_pos (i : ι) : 0<fusionWidthMenuDivisor w U i := by
  unfold fusionWidthMenuDivisor
  exact_mod_cast (Nat.card_pos (α := Subgroup.normalizer
    (U i:Set (Equiv.Perm (Fin (w i))))))

def fusionWidthPhysicalRow
    (D α : ∀ i, {N : Subgroup (U i) // N.Normal} → ℝ) : ℕ → ℕ → ℝ :=
  fusionWidthColdRow (fun j : FusionWidthMenuAxis w U => w j.1)
    (fun j => D j.1 j.2) (fun j => fusionWidthMenuDivisor w U j.1) (fun j => α j.1 j.2)

/-- A literal finite cover gives the actual normalized recurrence, with
each original action, normal axis, divisor and complement retained. -/
theorem fusionWidthPhysicalUnion_recurrence
    (hw : ∀ i, 0<w i) (n : ℕ) (hn : ∀ i, w i≤n)
    (F : Set (Subgroup (Equiv.Perm (Fin n))))
    (P : ∀ i, Subgroup (U i × Equiv.Perm (Fin (n-w i))) → Prop)
    (hP : ∀ i, FusionOrbitNatural (U i) (P i))
    (hcover : ∀ H∈F, ∃ i, H∈FusionWidthCanonicalFamily (U i) (hn i) (P i))
    (D α : ∀ i, {N : Subgroup (U i) // N.Normal} → ℝ)
    (henvelope : ∀ i N J, fusionSurvivingEpiCount (U i) (P i) N J ≤
      D i N*(2:ℝ)^(α i N*((n-w i:ℕ):ℝ))) :
    (Nat.card F:ℝ)/exactBenchmark n ≤
      ∑ b ∈ Finset.range n, fusionWidthPhysicalRow w U D α n b *
        ((subgroupCount b:ℝ)/exactBenchmark b) := by
  have hcard := fusionPhysicalUnion_card_le F
    (fun i => FusionWidthCanonicalFamily (U i) (hn i) (P i)) hcover
  have hcardR : (Nat.card F:ℝ) ≤
      ∑ i, (Nat.card (FusionWidthCanonicalFamily (U i) (hn i) (P i)):ℝ) := by
    exact_mod_cast hcard
  have hlocal (i : ι) : (Nat.card (FusionWidthCanonicalFamily (U i) (hn i) (P i)):ℝ)/
      exactBenchmark n ≤
      ∑ N : {N : Subgroup (U i) // N.Normal},
        fusionWidthColdKernel (n-w i) (w i) (D i N) (fusionWidthMenuDivisor w U i) (α i N) *
          ((subgroupCount (n-w i):ℝ)/exactBenchmark (n-w i)) := by
    rw [fusionWidthCanonicalFamily_card]
    simpa only [Nat.sub_add_cancel (hn i),fusionWidthMenuDivisor] using
      fusionWidthPhysical_bound (U i) (n-w i) (P i) (hP i) (D i) (α i) (henvelope i)
  calc
    _ ≤ (∑ i, (Nat.card (FusionWidthCanonicalFamily (U i) (hn i) (P i)):ℝ))/
        exactBenchmark n := div_le_div_of_nonneg_right hcardR (exactBenchmark_pos n).le
    _ = ∑ i, (Nat.card (FusionWidthCanonicalFamily (U i) (hn i) (P i)):ℝ)/
        exactBenchmark n := Finset.sum_div _ _ _
    _ ≤ ∑ i, ∑ N : {N : Subgroup (U i) // N.Normal},
        fusionWidthColdKernel (n-w i) (w i) (D i N) (fusionWidthMenuDivisor w U i) (α i N) *
          ((subgroupCount (n-w i):ℝ)/exactBenchmark (n-w i)) :=
      Finset.sum_le_sum (fun i _ => hlocal i)
    _ = _ := by
      unfold fusionWidthPhysicalRow
      rw [fusionWidthColdRow_weighted_sum
        (fun j : FusionWidthMenuAxis w U => w j.1)
        (fun j => D j.1 j.2) (fun j => fusionWidthMenuDivisor w U j.1)
        (fun j => α j.1 j.2) (fun j => hw j.1) _ n (fun j => hn j.1)]
      rw [Fintype.sum_sigma]

theorem fusionWidthPhysicalRow_nonneg
    (D α : ∀ i, {N : Subgroup (U i) // N.Normal} → ℝ)
    (hD : ∀ i N, 0≤D i N) (n b : ℕ) :
    0≤fusionWidthPhysicalRow w U D α n b :=
  fusionWidthColdRow_nonneg (fun j : FusionWidthMenuAxis w U => w j.1)
    (fun j => D j.1 j.2) (fun j => fusionWidthMenuDivisor w U j.1) (fun j => α j.1 j.2)
    (fun j => hD j.1 j.2) (fun j => fusionWidthMenuDivisor_pos w U j.1) n b

theorem fusionWidthPhysicalRow_forward
    (D α : ∀ i, {N : Subgroup (U i) // N.Normal} → ℝ)
    (hw : ∀ i, 0<w i) {n b : ℕ} (hn : n≤b) :
    fusionWidthPhysicalRow w U D α n b=0 :=
  fusionWidthColdRow_forward (fun j : FusionWidthMenuAxis w U => w j.1)
    (fun j => D j.1 j.2) (fun j => fusionWidthMenuDivisor w U j.1) (fun j => α j.1 j.2)
    (fun j => hw j.1) hn

theorem fusionWidthPhysicalRow_decay
    (D α : ∀ i, {N : Subgroup (U i) // N.Normal} → ℝ)
    (hw : ∀ i, 0<w i) (hD : ∀ i N, 0≤D i N)
    (hgap : ∀ i N, α i N<(halfDegree (w i):ℝ)/4) :
    ∃ C κ : ℝ, 0<C ∧ 0<κ ∧ ∀ᶠ n : ℕ in atTop,
      ∑ b ∈ Finset.range n, fusionWidthPhysicalRow w U D α n b≤C*(2:ℝ)^(-κ*(n:ℝ)) :=
  fusionWidthColdRow_decay (fun j : FusionWidthMenuAxis w U => w j.1)
    (fun j => D j.1 j.2) (fun j => fusionWidthMenuDivisor w U j.1) (fun j => α j.1 j.2)
    (fun j => hw j.1) (fun j => hD j.1 j.2)
    (fun j => fusionWidthMenuDivisor_pos w U j.1) (fun j => hgap j.1 j.2)

theorem fusionWidthPhysicalRow_contractive
    (D α : ∀ i, {N : Subgroup (U i) // N.Normal} → ℝ)
    (hw : ∀ i, 0<w i) (hD : ∀ i N, 0≤D i N)
    (hgap : ∀ i N, α i N<(halfDegree (w i):ℝ)/4) :
    ∀ᶠ n : ℕ in atTop,
      ∑ b ∈ Finset.range n, fusionWidthPhysicalRow w U D α n b≤1/2 :=
  fusionWidthColdRow_contractive (fun j : FusionWidthMenuAxis w U => w j.1)
    (fun j => D j.1 j.2) (fun j => fusionWidthMenuDivisor w U j.1) (fun j => α j.1 j.2)
    (fun j => hw j.1) (fun j => hD j.1 j.2)
    (fun j => fusionWidthMenuDivisor_pos w U j.1) (fun j => hgap j.1 j.2)

end Menu
end SymmetricSubgroupAsymptotics
