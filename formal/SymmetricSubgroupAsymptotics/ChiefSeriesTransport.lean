import SymmetricSubgroupAsymptotics.SimpleChiefFamilies

/-! Transport symbolic chief charts back to an original group through
an actual group equivalence. Every subgroup is the literal inverse image;
original quotient factors and their weights are proved to agree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {G R:Type} [Group G] [Group R]

/-- The original factor is identified by its actual quotient map. -/
def normalChainQuotientComapEquiv (e:R≃*G) (B L:Subgroup G) [B.Normal] [L.Normal] :
    normalChainQuotient (B.comap e.toMonoidHom) (L.comap e.toMonoidHom)≃*
      normalChainQuotient B L := by
  let q := QuotientGroup.congr (B.comap e.toMonoidHom) B e
    (Subgroup.map_comap_eq_self_of_surjective (f:=e.toMonoidHom) e.surjective B)
  have h : (normalChainQuotient (B.comap e.toMonoidHom) (L.comap e.toMonoidHom)).map
      q.toMonoidHom=normalChainQuotient B L := by
    dsimp only [normalChainQuotient]
    rw [Subgroup.map_map]
    have hq : q.toMonoidHom.comp (QuotientGroup.mk' (B.comap e.toMonoidHom))=
        (QuotientGroup.mk' B).comp e.toMonoidHom := MonoidHom.ext (fun _=>rfl)
    rw [hq,←Subgroup.map_map,
      Subgroup.map_comap_eq_self_of_surjective (f:=e.toMonoidHom) e.surjective L]
  exact (q.subgroupMap _).trans (MulEquiv.subgroupCongr h)

/-- Literal original subgroups, with chief minimality transported by
surjectivity and injectivity of the supplied equivalence. -/
def actualChiefSeriesComap (e:R≃*G) (s:ActualChiefSeries G) : ActualChiefSeries R where
  length := s.length
  subgroup := fun i=>(s.subgroup i).comap e.toMonoidHom
  normal i := inferInstance
  head := by
    rw [s.head,MonoidHom.comap_bot,(MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective]
  last := by rw [s.last,Subgroup.comap_top]
  step i := by
    apply lt_of_le_of_ne (Subgroup.comap_mono (s.step i).le)
    intro he
    exact (s.step i).ne (Subgroup.comap_injective e.surjective he)
  chief i K hK hlo hhi := by
    have hKM : (K.map e.toMonoidHom).Normal := Subgroup.Normal.map hK _ e.surjective
    have hlo' : s.subgroup i.castSucc ≤ K.map e.toMonoidHom := by
      have h := Subgroup.map_mono (f:=e.toMonoidHom) hlo
      rwa [Subgroup.map_comap_eq_self_of_surjective (f:=e.toMonoidHom)
        e.surjective (s.subgroup i.castSucc)] at h
    have hhi' : K.map e.toMonoidHom ≤ s.subgroup i.succ :=
      Subgroup.map_le_iff_le_comap.mpr hhi
    rcases s.chief i _ hKM hlo' hhi' with h|h
    · left
      have he := congrArg (Subgroup.comap e.toMonoidHom) h
      simpa only [Subgroup.comap_map_eq_self_of_injective (f:=e.toMonoidHom)
        e.injective K] using he
    · right
      have he := congrArg (Subgroup.comap e.toMonoidHom) h
      simpa only [Subgroup.comap_map_eq_self_of_injective (f:=e.toMonoidHom)
        e.injective K] using he

theorem actualChiefSeriesComap_weight (e:R≃*G) (s:ActualChiefSeries G) :
    actualChiefSeriesTernaryWeight (actualChiefSeriesComap e s)=actualChiefSeriesTernaryWeight s := by
  apply Finset.sum_congr rfl
  intro i _
  exact chiefTernaryWeight_congr (normalChainQuotientComapEquiv e
    (s.subgroup i.castSucc) (s.subgroup i.succ))

theorem alternatingChiefSeries_zero_of_equiv (n:ℕ) (hn:5 ≤ n)
    (e:R≃*alternatingGroup (Fin n)) :
    ∃s:ActualChiefSeries R,actualChiefSeriesTernaryWeight s=0 := by
  obtain ⟨s,hs⟩ := alternatingChiefSeries_zero n hn
  exact ⟨actualChiefSeriesComap e s,(actualChiefSeriesComap_weight e s).trans hs⟩

theorem symmetricChiefSeries_zero_of_equiv (n:ℕ) (hn:5 ≤ n)
    (e:R≃*Equiv.Perm (Fin n)) :
    ∃s:ActualChiefSeries R,actualChiefSeriesTernaryWeight s=0 := by
  obtain ⟨s,hs⟩ := symmetricChiefSeries_zero n hn
  exact ⟨actualChiefSeriesComap e s,(actualChiefSeriesComap_weight e s).trans hs⟩

end SymmetricSubgroupAsymptotics
