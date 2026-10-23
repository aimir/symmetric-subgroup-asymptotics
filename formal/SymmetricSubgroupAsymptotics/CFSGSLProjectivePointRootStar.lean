import SymmetricSubgroupAsymptotics.CFSGSymplecticIndexStarSubgroup

/-! Reusable point-root star through any faithful actual SL embedding.
Centrality in the target pulls back to the SAME SL source, so the
point-root chart remains injective after the target centre quotient.
This isolates the common C/B geometry from their matrix realizations. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSLProjectivePointRootStar
open CFSGTypeAProjectivePointRoots CFSGTypeAColumnFormCoordinates CFSGTypeABlockEmbedding
open CFSGTypeAColumnRootConjugacy
variable (K : Type) [Field K] (s : ℕ) {G : Type} [Group G]

abbrev SL := CFSGSymplecticIndexStarSubgroup.StarSL K s
abbrev Forms := CFSGSymplecticIndexStarSubgroup.StarForms K s

local instance parameterCommGroup : CommGroup (Multiplicative (Forms K s)) := inferInstance

variable (f : SL K s →* G)

def starHom : Multiplicative (Forms K s) →* G⧸Subgroup.center G :=
  ((QuotientGroup.mk' (Subgroup.center G)).comp f).comp
    (pointRootSLHom (firstVector (F:=K) (n:=Fin (s+2))))

theorem starHom_injective (hf : Function.Injective f) :
    Function.Injective (starHom K s f) := by
  apply (MonoidHom.ker_eq_bot_iff (starHom K s f)).mp
  apply bot_unique
  intro x hx
  have hc : f (pointRootSLHom firstVector x)∈Subgroup.center G :=
    (QuotientGroup.eq_one_iff _).mp hx
  have hsource : pointRootSLHom firstVector x∈Subgroup.center (SL K s) := by
    apply Subgroup.mem_center_iff.mpr
    intro A
    apply hf
    rw [map_mul,map_mul]
    exact (Subgroup.mem_center_iff.mp hc) (f A)
  have he := pointRootSL_eq_one_of_mem_center
    (CFSGSymplecticIndexStarSubgroup.firstVector_ne_zero K s) x hsource
  have hp : pointRootHom firstVector x=1 := by
    change projection (pointRootSLHom firstVector x)=1
    rw [he,map_one]
  exact Subgroup.mem_bot.mpr
    (pointRootHom_injective (CFSGSymplecticIndexStarSubgroup.firstVector_ne_zero K s)
      (hp.trans (map_one (pointRootHom firstVector)).symm))

def starRoot : Subgroup (G⧸Subgroup.center G) := (starHom K s f).range

def starRootEquiv (hf : Function.Injective f) : Multiplicative (Forms K s) ≃* starRoot K s f :=
  MonoidHom.ofInjective (starHom_injective K s f hf)

theorem starRoot_card (hf : Function.Injective f) :
    Nat.card (starRoot K s f)=Nat.card K^(s+2) := by
  calc
    Nat.card (starRoot K s f)=Nat.card (Multiplicative (Forms K s)) :=
      Nat.card_congr (starRootEquiv K s f hf).symm.toEquiv
    _ = Nat.card (pointRoot (firstVector (F:=K) (n:=Fin (s+2)))) :=
      Nat.card_congr (pointRootEquiv
        (CFSGSymplecticIndexStarSubgroup.firstVector_ne_zero K s)).toEquiv
    _ = _ := by
      rw [pointRoot_card (CFSGSymplecticIndexStarSubgroup.firstVector_ne_zero K s),
        Fintype.card_sum,Fintype.card_unit,Fintype.card_fin]
      congr 1
      omega

theorem star_nonidentity_conjugate (a b : starRoot K s f) (ha : a≠1) (hb : b≠1) :
    ∃ z : G⧸Subgroup.center G, z*(a : G⧸Subgroup.center G)*z⁻¹=b := by
  obtain ⟨u,hu⟩ := a.property
  obtain ⟨v,hv⟩ := b.property
  have hu0 : u.toAdd≠0 := by
    intro he
    apply ha
    apply Subtype.ext
    rw [←hu,show u=1 from congrArg Multiplicative.ofAdd he,map_one]
    rfl
  have hv0 : v.toAdd≠0 := by
    intro he
    apply hb
    apply Subtype.ext
    rw [←hv,show v=1 from congrArg Multiplicative.ofAdd he,map_one]
    rfl
  obtain ⟨A,hA⟩ := exists_form_conjugator (F:=K) (0 : Fin (s+2))
    (⟨1,by omega⟩ : Fin (s+2))
    (by intro he; have hh:=congrArg Fin.val he; change 0=1 at hh; omega)
    u.toAdd v.toAdd hu0 hv0
  let j := (QuotientGroup.mk' (Subgroup.center G)).comp f
  refine ⟨j A,?_⟩
  rw [←hu,←hv]
  change j A*j (transvectionSL u.toAdd.property)*(j A)⁻¹=j (transvectionSL v.toAdd.property)
  have he := congrArg j hA
  simpa only [map_mul,map_inv] using he

end SymmetricSubgroupAsymptotics.CFSGSLProjectivePointRootStar
