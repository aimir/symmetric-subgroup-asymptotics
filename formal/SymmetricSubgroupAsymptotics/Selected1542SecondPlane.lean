import SymmetricSubgroupAsymptotics.Selected1542FirstQuotient
import SymmetricSubgroupAsymptotics.Selected1542SecondPlaneReceipts
import SymmetricSubgroupAsymptotics.ThreeCycleMinimalNormal

/-! Actual minimality of the same N8/Z follows from its three nonidentity
cosets and the actual cubic conjugation cycle. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Selected1542QuotientStructure

def secondPlane (j : Fin 3) : FirstQuotient :=
  QuotientGroup.mk' originalFirstAxis (normalOriginal (secondPlaneIndex j))

def firstQuotientCubicLift : FirstQuotient := QuotientGroup.mk' originalFirstAxis (source 0)

private theorem mkFirst_eq_of_residue (g h : Original)
    (he : g.val=h.val ∨ g.val=h.val*firstCenterZ) :
    QuotientGroup.mk' originalFirstAxis g=QuotientGroup.mk' originalFirstAxis h := by
  rcases he with he | he
  · exact congrArg (QuotientGroup.mk' originalFirstAxis) (Subtype.ext he)
  · have hg : g=h*originalCentralInvolution := Subtype.ext he
    rw [hg,map_mul,mkFirst_involution,mul_one]

theorem secondPlane_mem (j : Fin 3) : secondPlane j∈secondAxis := by
  exact ⟨normalOriginal (secondPlaneIndex j),(normalTable.chart (secondPlaneIndex j)).property,rfl⟩

theorem secondPlane_ne_one (j : Fin 3) : secondPlane j≠1 := by
  intro h
  rcases (mkFirst_eq_one_iff _).mp h with he | he
  · obtain ⟨p,hp⟩ := (secondPlane_nonzero j).1
    exact hp (congrArg (fun g : Original => g.val p) he)
  · obtain ⟨p,hp⟩ := (secondPlane_nonzero j).2
    exact hp (congrArg (fun g : Original => g.val p) he)

theorem secondPlane_cycle_actual (j : Fin 3) :
    firstQuotientCubicLift*secondPlane j*firstQuotientCubicLift⁻¹=secondPlane (j+1) := by
  have he : (source 0*normalOriginal (secondPlaneIndex j)*(source 0)⁻¹).val=
      (normalOriginal (secondPlaneIndex (j+1))).val ∨
      (source 0*normalOriginal (secondPlaneIndex j)*(source 0)⁻¹).val=
        (normalOriginal (secondPlaneIndex (j+1))).val*firstCenterZ := by
    rcases secondPlane_cycle j with h | h
    · exact Or.inl (Equiv.ext h)
    · exact Or.inr (Equiv.ext h)
  simpa only [map_mul,map_inv,firstQuotientCubicLift,secondPlane] using
    mkFirst_eq_of_residue _ _ he

theorem secondAxis_nonzero_cover (x : FirstQuotient) (hx : x∈secondAxis) (hxne : x≠1) :
    ∃ j : Fin 3, x=secondPlane j := by
  obtain ⟨g,hg,rfl⟩ := hx
  obtain ⟨n,hn⟩ := normalTable.chart_surjective ⟨g,hg⟩
  have hgn : g=normalOriginal n := (congrArg Subtype.val hn).symm
  rw [hgn] at hxne ⊢
  rcases secondPlane_cover n with h | h | ⟨j,h⟩
  · have he : normalOriginal n=1 := Subtype.ext (Equiv.ext h)
    exact False.elim (hxne (by rw [he,map_one]))
  · have he : normalOriginal n=originalCentralInvolution := Subtype.ext (Equiv.ext h)
    exact False.elim (hxne (by rw [he]; exact mkFirst_involution))
  · refine ⟨j,?_⟩
    apply mkFirst_eq_of_residue
    rcases h with h | h
    · exact Or.inl (Equiv.ext h)
    · exact Or.inr (Equiv.ext h)

theorem secondAxis_minimalNormal : IsMinimalNormalSubgroup secondAxis := by
  have hne : secondAxis≠⊥ := by
    intro hb
    have h := secondPlane_mem 0
    rw [hb] at h
    exact secondPlane_ne_one 0 (Subgroup.mem_bot.mp h)
  exact minimalNormal_of_three_cycle secondAxis hne firstQuotientCubicLift secondPlane
    secondAxis_nonzero_cover secondPlane_cycle_actual

end SymmetricSubgroupAsymptotics.Selected1542QuotientStructure
