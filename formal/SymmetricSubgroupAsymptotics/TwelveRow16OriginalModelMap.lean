import SymmetricSubgroupAsymptotics.TwelveRow16SymmetricProductModel

/-! Ordinary source generation recovers the exact original row16 range.
Only short words in the original three generators are used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwelveRow16SymmetricProductModel
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoTwelvePairFiniteCatalogue
open DihedralGroup

private theorem dihedral_hom_mem {P : Type} [Group P] (f : D →* P)
    (K : Subgroup P) (hr : f (r 1)∈K) (hs : f (sr 0)∈K) (g : D) : f g∈K := by
  have hrpow : ∀ i : ZMod 3,(r i : D)=(r 1)^i.val := by decide +kernel
  have hsr : ∀ i : ZMod 3,(sr i : D)=sr 0*(r 1)^i.val := by decide +kernel
  cases g with
  | r i => rw [hrpow,map_pow]; exact K.pow_mem hr _
  | sr i => rw [hsr,map_mul,map_pow]; exact K.mul_mem hs (K.pow_mem hr _)

/-- The displayed three lifts generate BOTH original D6 factors. -/
theorem source_generation : Subgroup.closure (Set.range lifts)=⊤ := by
  let K := Subgroup.closure (Set.range lifts)
  let t := lifts 0
  let u := lifts 1
  let v := lifts 2
  have ht : t∈K := Subgroup.subset_closure (Set.mem_range_self 0)
  have hu : u∈K := Subgroup.subset_closure (Set.mem_range_self 1)
  have hv : v∈K := Subgroup.subset_closure (Set.mem_range_self 2)
  have hrR : ((1,r 1) : Source)∈K := by
    have h := K.mul_mem (K.mul_mem (K.mul_mem ht hu) (K.inv_mem ht)) hu
    have he : t*u*t⁻¹*u=((1,r 1) : Source) := by decide +kernel
    rwa [he] at h
  have hrL : ((r 1,1) : Source)∈K := by
    have h := K.mul_mem (K.pow_mem ht 2) (K.inv_mem hrR)
    have he : t^2*((1,r 1) : Source)⁻¹=((r 1,1) : Source) := by decide +kernel
    rwa [he] at h
  have hsL : ((sr 0,1) : Source)∈K := by
    have h := K.mul_mem hv hu
    have he : v*u=((sr 0,1) : Source) := by decide +kernel
    rwa [he] at h
  have hsR : ((1,sr 0) : Source)∈K := hu
  apply top_unique
  rintro ⟨a,b⟩ _
  have ha := dihedral_hom_mem (MonoidHom.inl D D) K hrL hsL a
  have hb := dihedral_hom_mem (MonoidHom.inr D D) K hrR hsR b
  simpa only [MonoidHom.inl_apply,MonoidHom.inr_apply,Prod.mk_mul_mk,
    mul_one,one_mul] using K.mul_mem ha hb

 theorem range_eq_original : action.range=Row16Top := by
  apply le_antisymm
  · have hpre : Subgroup.closure (Set.range lifts)≤Row16Top.comap action := by
      apply (Subgroup.closure_le (Row16Top.comap action)).mpr
      rintro _ ⟨i,rfl⟩
      change action (lifts i)∈Row16Top
      rw [bindings]
      exact Subgroup.subset_closure (Set.mem_range_self i)
    rw [source_generation] at hpre
    rintro _ ⟨g,rfl⟩
    exact hpre (Subgroup.mem_top g)
  · apply (Subgroup.closure_le action.range).mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨lifts i,bindings i⟩

def originalMap : Source →* Row16Top :=
  (MulEquiv.subgroupCongr range_eq_original).toMonoidHom.comp action.rangeRestrict

theorem originalMap_surjective : Function.Surjective originalMap :=
  (MulEquiv.subgroupCongr range_eq_original).surjective.comp action.rangeRestrict_surjective

def originalEquiv : Source ≃* Row16Top := MulEquiv.ofBijective originalMap
  ⟨fun _ _ h => action_injective (congrArg (fun z : Row16Top => (z : Equiv.Perm (Fin 12))) h),originalMap_surjective⟩

end SymmetricSubgroupAsymptotics.TwelveRow16SymmetricProductModel
