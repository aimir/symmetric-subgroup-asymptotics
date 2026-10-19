import SymmetricSubgroupAsymptotics.TwelveRow18DihedralCentralModel

/-! Ordinary source generation recovers the exact original row18 range.
Only short words in the original three generators are used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwelveRow18DihedralCentralModel
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwelvePairFiniteCatalogue
open DihedralGroup
open TernaryFourBlockKleinSocles (Bit)

private theorem dihedral_hom_mem {P : Type} [Group P] (f : D →* P)
    (K : Subgroup P) (hr : f (r 1)∈K) (hs : f (sr 0)∈K) (g : D) : f g∈K := by
  have hrpow : ∀ i : ZMod 3,(r i : D)=(r 1)^i.val := by decide +kernel
  have hsr : ∀ i : ZMod 3,(sr i : D)=sr 0*(r 1)^i.val := by decide +kernel
  cases g with
  | r i => rw [hrpow,map_pow]; exact K.pow_mem hr _
  | sr i => rw [hsr,map_mul,map_pow]; exact K.mul_mem hs (K.pow_mem hr _)

/-- The three original lifts recover the dihedral, central cubic and binary factors. -/
theorem source_generation : Subgroup.closure (Set.range lifts)=⊤ := by
  let K := Subgroup.closure (Set.range lifts)
  let t := lifts 0
  let u := lifts 1
  let v := lifts 2
  have ht : t∈K := Subgroup.subset_closure (Set.mem_range_self 0)
  have hu : u∈K := Subgroup.subset_closure (Set.mem_range_self 1)
  have hv : v∈K := Subgroup.subset_closure (Set.mem_range_self 2)
  have hr : (((r 1,1),1) : Source)∈K := by
    have h := K.mul_mem (K.mul_mem (K.mul_mem ht hu) (K.inv_mem ht)) hu
    have he : t*u*t⁻¹*u=(((r 1,1),1) : Source) := by decide +kernel
    rwa [he] at h
  have hc : (((1,Multiplicative.ofAdd 1),1) : Source)∈K := by
    have h := K.mul_mem (K.pow_mem ht 2) (K.inv_mem hr)
    have he : t^2*(((r 1,1),1) : Source)⁻¹=
        (((1,Multiplicative.ofAdd 1),1) : Source) := by decide +kernel
    rwa [he] at h
  apply top_unique
  rintro ⟨⟨a,c⟩,b⟩ _
  let f : D →* Source := (MonoidHom.inl (D × C3) Bit).comp (MonoidHom.inl D C3)
  have hfr : f (r 1)∈K := by change (((r 1,1),1) : Source)∈K; exact hr
  have hfs : f (sr 0)∈K := by change (((sr 0,1),1) : Source)∈K; exact hu
  have ha := dihedral_hom_mem f K hfr hfs a
  have hcpow : ∀ c : C3, (((1,c),1) : Source)=
      (((1,Multiplicative.ofAdd 1),1) : Source)^c.toAdd.val := by decide +kernel
  have hcmem : (((1,c),1) : Source)∈K := by
    rw [hcpow]
    exact K.pow_mem hc _
  have hb : (((1,1),b) : Source)∈K := by
    have hcases : b=1 ∨ b=Multiplicative.ofAdd 1 :=
      (show ∀ b : Bit,b=1 ∨ b=Multiplicative.ofAdd 1 by decide +kernel) b
    rcases hcases with rfl | rfl
    · exact K.one_mem
    · exact hv
  have h := K.mul_mem (K.mul_mem ha hcmem) hb
  simpa [f] using h

 theorem range_eq_original : action.range=Row18Top := by
  apply le_antisymm
  · have hpre : Subgroup.closure (Set.range lifts)≤Row18Top.comap action := by
      apply (Subgroup.closure_le (Row18Top.comap action)).mpr
      rintro _ ⟨i,rfl⟩
      change action (lifts i)∈Row18Top
      rw [bindings]
      exact Subgroup.subset_closure (Set.mem_range_self i)
    rw [source_generation] at hpre
    rintro _ ⟨g,rfl⟩
    exact hpre (Subgroup.mem_top g)
  · apply (Subgroup.closure_le action.range).mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨lifts i,bindings i⟩

def originalMap : Source →* Row18Top :=
  (MulEquiv.subgroupCongr range_eq_original).toMonoidHom.comp action.rangeRestrict

theorem originalMap_surjective : Function.Surjective originalMap :=
  (MulEquiv.subgroupCongr range_eq_original).surjective.comp action.rangeRestrict_surjective

def originalEquiv : Source ≃* Row18Top := MulEquiv.ofBijective originalMap
  ⟨fun _ _ h => action_injective (congrArg (fun z : Row18Top => (z : Equiv.Perm (Fin 12))) h),originalMap_surjective⟩

end SymmetricSubgroupAsymptotics.TwelveRow18DihedralCentralModel
