import SymmetricSubgroupAsymptotics.ChiefAbelianCompositionLength
import SymmetricSubgroupAsymptotics.NormalChainQuotientSurjectiveComap
import SymmetricSubgroupAsymptotics.SimpleChiefFamilies

/-!
# Prepending a minimal normal subgroup to a quotient chief series

Pull a literal chief series of `G/E` back along the quotient map and prepend
`⊥ < E`.  The construction retains every normal section and proves the
exact abelian chief-length recursion.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

variable {G : Type} [Group G]
variable (E : Subgroup G) [E.Normal]

/-- Pull a quotient chief series back to `G` and prepend the minimal normal
kernel. -/
def prependMinimalNormalChiefSeries
    (hE : E ≠ ⊥)
    (hmin : ∀ K : Subgroup G, K.Normal → K ≤ E → K = ⊥ ∨ K = E)
    (s : ActualChiefSeries (G ⧸ E)) : ActualChiefSeries G where
  length := s.length + 1
  subgroup := Fin.cases ⊥
    (fun i => (s.subgroup i).comap (QuotientGroup.mk' E))
  normal i := by
    refine Fin.cases (show (⊥ : Subgroup G).Normal by infer_instance) ?_ i
    intro j
    exact (s.normal j).comap (QuotientGroup.mk' E)
  head := rfl
  last := by
    change (s.subgroup (Fin.last s.length)).comap (QuotientGroup.mk' E) = ⊤
    simp [s.last]
  step i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · change (⊥ : Subgroup G) <
        (s.subgroup 0).comap (QuotientGroup.mk' E)
      rw [s.head, MonoidHom.comap_bot, QuotientGroup.ker_mk']
      exact (bot_lt_iff_ne_bot).mpr hE
    · change (s.subgroup j.castSucc).comap (QuotientGroup.mk' E) <
        (s.subgroup j.succ).comap (QuotientGroup.mk' E)
      exact (Subgroup.comap_lt_comap_of_surjective
        (QuotientGroup.mk'_surjective E)).mpr (s.step j)
  chief i K hK hlo hhi := by
    revert hlo hhi
    refine Fin.cases ?_ (fun j => ?_) i
    · intro hlo hhi
      change (⊥ : Subgroup G) ≤ K at hlo
      change K ≤ (s.subgroup 0).comap (QuotientGroup.mk' E) at hhi
      rw [s.head, MonoidHom.comap_bot, QuotientGroup.ker_mk'] at hhi
      rcases hmin K hK hhi with he | he
      · exact Or.inl he
      · right
        rw [he]
        change E = (s.subgroup 0).comap (QuotientGroup.mk' E)
        rw [s.head, MonoidHom.comap_bot, QuotientGroup.ker_mk']
    · intro hlo hhi
      change (s.subgroup j.castSucc).comap (QuotientGroup.mk' E) ≤ K at hlo
      change K ≤ (s.subgroup j.succ).comap (QuotientGroup.mk' E) at hhi
      let q := QuotientGroup.mk' E
      have hker : q.ker ≤ K := by
        calc
          q.ker ≤ (s.subgroup j.castSucc).comap q :=
            Subgroup.ker_le_comap q (s.subgroup j.castSucc)
          _ ≤ K := hlo
      have hlo' : s.subgroup j.castSucc ≤ K.map q := by
        rw [← Subgroup.map_comap_eq_self_of_surjective
          (QuotientGroup.mk'_surjective E) (s.subgroup j.castSucc)]
        exact Subgroup.map_mono hlo
      have hhi' : K.map q ≤ s.subgroup j.succ := by
        rw [← Subgroup.map_comap_eq_self_of_surjective
          (QuotientGroup.mk'_surjective E) (s.subgroup j.succ)]
        exact Subgroup.map_mono hhi
      have hmapNormal : (K.map q).Normal :=
        hK.map q (QuotientGroup.mk'_surjective E)
      rcases s.chief j (K.map q) hmapNormal hlo' hhi' with he | he
      · left
        calc
          K = (K.map q).comap q := (Subgroup.comap_map_eq_self hker).symm
          _ = (s.subgroup j.castSucc).comap q := congrArg (Subgroup.comap q) he
      · right
        calc
          K = (K.map q).comap q := (Subgroup.comap_map_eq_self hker).symm
          _ = (s.subgroup j.succ).comap q := congrArg (Subgroup.comap q) he

@[simp] theorem prependMinimalNormalChiefSeries_length
    (hE : E ≠ ⊥)
    (hmin : ∀ K : Subgroup G, K.Normal → K ≤ E → K = ⊥ ∨ K = E)
    (s : ActualChiefSeries (G ⧸ E)) :
    (prependMinimalNormalChiefSeries E hE hmin s).length = s.length + 1 := rfl

@[simp] theorem prependMinimalNormalChiefSeries_subgroup_zero
    (hE : E ≠ ⊥)
    (hmin : ∀ K : Subgroup G, K.Normal → K ≤ E → K = ⊥ ∨ K = E)
    (s : ActualChiefSeries (G ⧸ E)) :
    (prependMinimalNormalChiefSeries E hE hmin s).subgroup 0 = ⊥ := rfl

@[simp] theorem prependMinimalNormalChiefSeries_subgroup_succ
    (hE : E ≠ ⊥)
    (hmin : ∀ K : Subgroup G, K.Normal → K ≤ E → K = ⊥ ∨ K = E)
    (s : ActualChiefSeries (G ⧸ E)) (i : Fin (s.length + 1)) :
    (prependMinimalNormalChiefSeries E hE hmin s).subgroup (Fin.succ i) =
      (s.subgroup i).comap (QuotientGroup.mk' E) := rfl

set_option maxHeartbeats 800000

/-- Exact abelian-edge recursion for the prepended series. -/
theorem prependMinimalNormalChiefSeries_abelianLength
    [Finite G]
    (hE : E ≠ ⊥)
    (hmin : ∀ K : Subgroup G, K.Normal → K ≤ E → K = ⊥ ∨ K = E)
    (s : ActualChiefSeries (G ⧸ E)) :
    actualChiefSeriesAbelianLength
        (prependMinimalNormalChiefSeries E hE hmin s) =
      chiefAbelianLength E + actualChiefSeriesAbelianLength s := by
  let q := QuotientGroup.mk' E
  let T := prependMinimalNormalChiefSeries E hE hmin s
  let F : Fin (s.length + 1) → ℕ := fun i =>
    chiefAbelianLength
      (normalChainQuotient (T.subgroup i.castSucc) (T.subgroup i.succ))
  unfold actualChiefSeriesAbelianLength
  change (∑ i, F i) = chiefAbelianLength E +
    ∑ i : Fin s.length, chiefAbelianLength
      (normalChainQuotient (s.subgroup i.castSucc) (s.subgroup i.succ))
  rw [Fin.sum_univ_succ]
  have hfirst : F 0 = chiefAbelianLength E := by
    dsimp [F, T]
    have hsub : (s.subgroup 0).comap (QuotientGroup.mk' E) = E := by
      rw [s.head, MonoidHom.comap_bot, QuotientGroup.ker_mk']
    exact chiefAbelianLength_congr
      ((normalChainQuotientBotEquiv
        ((s.subgroup 0).comap (QuotientGroup.mk' E))).trans
          (MulEquiv.subgroupCongr hsub))
  rw [hfirst]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change F i.succ = chiefAbelianLength
    (normalChainQuotient (s.subgroup i.castSucc) (s.subgroup i.succ))
  dsimp [F, T]
  change chiefAbelianLength
      (normalChainQuotient
        ((s.subgroup i.castSucc).comap q)
        ((s.subgroup i.succ).comap q)) =
    chiefAbelianLength
      (normalChainQuotient (s.subgroup i.castSucc) (s.subgroup i.succ))
  exact chiefAbelianLength_congr
    (normalChainQuotientComapSurjectiveEquiv q
      (QuotientGroup.mk'_surjective E)
      (s.subgroup i.castSucc) (s.subgroup i.succ) (s.step i).le)

/-- Exact nonabelian-interval recursion for the prepended series. -/
theorem prependMinimalNormalChiefSeries_nonabelianCount
    [Finite G]
    (hE : E ≠ ⊥)
    (hmin : ∀ K : Subgroup G, K.Normal → K ≤ E → K = ⊥ ∨ K = E)
    (s : ActualChiefSeries (G ⧸ E)) :
    actualChiefSeriesNonabelianCount
        (prependMinimalNormalChiefSeries E hE hmin s) =
      chiefNonabelianIndicator E + actualChiefSeriesNonabelianCount s := by
  let q := QuotientGroup.mk' E
  let T := prependMinimalNormalChiefSeries E hE hmin s
  let F : Fin (s.length + 1) → ℕ := fun i =>
    chiefNonabelianIndicator
      (normalChainQuotient (T.subgroup i.castSucc) (T.subgroup i.succ))
  unfold actualChiefSeriesNonabelianCount
  change (∑ i, F i) = chiefNonabelianIndicator E +
    ∑ i : Fin s.length, chiefNonabelianIndicator
      (normalChainQuotient (s.subgroup i.castSucc) (s.subgroup i.succ))
  rw [Fin.sum_univ_succ]
  have hfirst : F 0 = chiefNonabelianIndicator E := by
    dsimp [F, T]
    have hsub : (s.subgroup 0).comap (QuotientGroup.mk' E) = E := by
      rw [s.head, MonoidHom.comap_bot, QuotientGroup.ker_mk']
    exact chiefNonabelianIndicator_congr
      ((normalChainQuotientBotEquiv
        ((s.subgroup 0).comap (QuotientGroup.mk' E))).trans
          (MulEquiv.subgroupCongr hsub))
  rw [hfirst]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change F i.succ = chiefNonabelianIndicator
    (normalChainQuotient (s.subgroup i.castSucc) (s.subgroup i.succ))
  dsimp [F, T]
  change chiefNonabelianIndicator
      (normalChainQuotient
        ((s.subgroup i.castSucc).comap q)
        ((s.subgroup i.succ).comap q)) =
    chiefNonabelianIndicator
      (normalChainQuotient (s.subgroup i.castSucc) (s.subgroup i.succ))
  exact chiefNonabelianIndicator_congr
    (normalChainQuotientComapSurjectiveEquiv q
      (QuotientGroup.mk'_surjective E)
      (s.subgroup i.castSucc) (s.subgroup i.succ) (s.step i).le)

end SymmetricSubgroupAsymptotics

end
