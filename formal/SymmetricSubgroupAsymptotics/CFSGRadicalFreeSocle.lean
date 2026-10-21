import SymmetricSubgroupAsymptotics.CFSGSolubleRadical
import SymmetricSubgroupAsymptotics.PrimitiveSocleCentralizerRegular

/-! Automorphism invariance and nonabelian minimal factors of the actual
socle in a radical-free finite group. These are elementary structural steps
for soluble generation; no classification or group-order formula is used. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGReduction

theorem minimalNormal_map {G Q : Type} [Group G] [Group Q]
    (e : G ≃* Q) (N : Subgroup G) (hN : IsMinimalNormalSubgroup N) :
    IsMinimalNormalSubgroup (N.map e.toMonoidHom) := by
  refine ⟨hN.1.map e.toMonoidHom e.surjective, ?_, ?_⟩
  · intro he
    apply hN.2.1
    exact (Subgroup.map_eq_bot_iff_of_injective N e.injective).mp he
  · intro K hK hKbot hKN
    letI := hK
    have hpre : K.comap e.toMonoidHom ≠ ⊥ := by
      intro he
      apply hKbot
      have hm := congrArg (fun L : Subgroup G => L.map e.toMonoidHom) he
      simpa only [Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective,
        Subgroup.map_bot] using hm
    have hle : K.comap e.toMonoidHom ≤ N := by
      have h := Subgroup.comap_mono (f := e.toMonoidHom) hKN
      rwa [Subgroup.comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective] at h
    have he := hN.2.2 (K.comap e.toMonoidHom) inferInstance hpre hle
    have hm := congrArg (fun L : Subgroup G => L.map e.toMonoidHom) he
    simpa only [Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective] using hm

instance finiteGroupSocle_characteristic (G : Type) [Group G] :
    (finiteGroupSocle G).Characteristic := by
  apply Subgroup.characteristic_iff_map_le.mpr
  intro a
  apply Subgroup.map_le_iff_le_comap.mpr
  apply Subgroup.normalClosure_le_normal
  rintro x ⟨N, hN, hx⟩
  change a x ∈ finiteGroupSocle G
  exact Subgroup.subset_normalClosure
    ⟨N.map a.toMonoidHom, minimalNormal_map a N hN, ⟨x, hx, rfl⟩⟩

theorem minimalNormal_noncommutative_of_radical_eq_bot
    {G : Type} [Group G] [Finite G] (hR : solubleRadical G = ⊥)
    (N : Subgroup G) (hN : IsMinimalNormalSubgroup N) :
    ¬ IsMulCommutative N := by
  intro hn
  letI := hN.1
  letI : IsSolvable N := isSolvable_of_comm (isMulCommutative_iff.mp hn)
  have hle := le_solubleRadical N
  rw [hR] at hle
  exact hN.2.1 (le_bot_iff.mp hle)

theorem finiteGroupSocle_ne_bot (G : Type) [Group G] [Finite G] [Nontrivial G] :
    finiteGroupSocle G ≠ ⊥ := by
  obtain ⟨N, hN⟩ := PrimitiveSocleONanScottHelpers.exists_minimalNormal (G := G)
  intro he
  apply hN.2.1
  apply le_bot_iff.mp
  intro x hx
  rw [← he]
  exact Subgroup.subset_normalClosure ⟨N, hN, hx⟩

end SymmetricSubgroupAsymptotics.CFSGReduction
