import SymmetricSubgroupAsymptotics.CFSGSLTwoBruhat
import SymmetricSubgroupAsymptotics.SylowActualNormalizerLift
import SymmetricSubgroupAsymptotics.CFSGRankOneCosetAction

/-! The original triangular subgroup, Sylow normalizer and two-cell
action of PSL2, using its actual quotient by the SL2 centre. All field
parameters and the defining characteristic are retained literally. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoGeometry
open Matrix CFSGTypeASLTwoWeyl CFSGSLTwoUpperRoots CFSGSLTwoUpperSylow
open CFSGPSLTwoRootCoordinates CFSGSLTwoBruhat
variable {F : Type*} [Field F]

def projectiveBorel : Subgroup (PSL (F:=F)) :=
  (borel (F:=F)).map (projection (F:=F))

def projectiveTorusHom : Fˣ →* PSL (F:=F) :=
  (projection (F:=F)).comp (torusHom (F:=F))

@[simp] theorem projectiveTorusHom_apply (c : Fˣ) :
    projectiveTorusHom c=projectiveTorus c := rfl

def pairTorus : Subgroup (PSL (F:=F)) := (projectiveTorusHom (F:=F)).range

theorem upperRoot_map_projection :
    (upperRoot (F:=F)).map (projection (F:=F))=projectiveRoot (F:=F) :=
  (MonoidHom.range_comp (projection (F:=F)) (upperHom (F:=F))).symm

theorem center_le_borel : Subgroup.center (SL2 (F:=F))≤borel (F:=F) := by
  intro g hg
  have he := Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center hg (0 : Fin 2)
  have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 0) he
  dsimp only at hh
  change g.val 1 0=0
  simpa [Matrix.scalar_apply] using hh.symm

theorem projection_mem_borel_iff (g : SL2 (F:=F)) :
    projection g∈projectiveBorel (F:=F) ↔ g∈borel (F:=F) := by
  constructor
  · rintro ⟨h,hh,he⟩
    have hc : h⁻¹*g∈Subgroup.center (SL2 (F:=F)) := QuotientGroup.eq.mp he
    have hm := (borel (F:=F)).mul_mem hh (center_le_borel hc)
    simpa only [mul_inv_cancel_left] using hm
  · intro hg
    exact ⟨g,hg,rfl⟩

theorem projectiveRoot_le_borel : projectiveRoot (F:=F)≤projectiveBorel (F:=F) := by
  rw [←upperRoot_map_projection]
  apply Subgroup.map_mono
  rintro g ⟨a,rfl⟩
  exact upper_entry10 _

theorem projective_torus_mem_borel (c : Fˣ) :
    projectiveTorus c∈projectiveBorel (F:=F) :=
  ⟨torusHom c,torus_mem_borel c,rfl⟩

theorem projectiveBorel_le_normalizer_root :
    projectiveBorel (F:=F)≤Subgroup.normalizer (projectiveRoot (F:=F) : Set (PSL (F:=F))) := by
  have hh := ((upperRoot (F:=F)).le_normalizer_map (projection (F:=F)))
  rw [normalizer_upper_eq_borel,upperRoot_map_projection] at hh
  exact hh

def projectiveSylow [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p] :
    Sylow p (PSL (F:=F)) :=
  (upperSylow (F:=F) (p:=p)).mapSurjective (f:=projection) projection_surjective

@[simp] theorem projectiveSylow_coe [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p] :
    (projectiveSylow (F:=F) p : Subgroup (PSL (F:=F)))=projectiveRoot (F:=F) :=
  upperRoot_map_projection

theorem normalizer_root_eq_borel_of_char [Finite F]
    (p : ℕ) [Fact p.Prime] [CharP F p] :
    Subgroup.normalizer (projectiveRoot (F:=F) : Set (PSL (F:=F)))=projectiveBorel (F:=F) := by
  apply le_antisymm _ projectiveBorel_le_normalizer_root
  intro x hx
  have hn : x∈Subgroup.normalizer
      (((upperSylow (F:=F) (p:=p) : Subgroup (SL2 (F:=F))).map projection) :
        Set (PSL (F:=F))) := by
    rwa [upperSylow_coe,upperRoot_map_projection]
  obtain ⟨g,hg,hgx⟩ := SylowActualNormalizerLift.exists_lift projection projection_surjective
    (upperSylow (F:=F) (p:=p)) x hn
  exact ⟨g,normalizer_le_borel hg,hgx⟩

theorem normalizer_projectiveRoot_eq_borel [Finite F] :
    Subgroup.normalizer (projectiveRoot (F:=F) : Set (PSL (F:=F)))=projectiveBorel (F:=F) := by
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨p,hchar,n,hp,_hn⟩ := FiniteField.card' F
  letI : CharP F p := hchar
  letI pslGeometryPrime : Fact p.Prime := ⟨hp⟩
  exact normalizer_root_eq_borel_of_char p

theorem projectiveWeyl_not_mem_borel : projectiveWeyl (F:=F)∉projectiveBorel (F:=F) := by
  intro hw
  have hm := (projection_mem_borel_iff (weyl (F:=F))).mp hw
  change (weyl (F:=F)).val 1 0=0 at hm
  rw [sl_weyl_coe] at hm
  exact neg_ne_zero.mpr one_ne_zero hm

theorem two_cells (g : PSL (F:=F)) :
    g∈projectiveBorel (F:=F) ∨
      ∃ (b : projectiveBorel (F:=F)) (u : projectiveRoot (F:=F)),
        g=b.val*projectiveWeyl*u.val := by
  obtain ⟨x,rfl⟩ := projection_surjective g
  rcases CFSGSLTwoBruhat.two_cells x with hx | ⟨b,u,he⟩
  · exact Or.inl ⟨x,hx,rfl⟩
  · have hu : projection u.val∈projectiveRoot (F:=F) := by
      rw [←upperRoot_map_projection]
      exact ⟨u.val,u.property,rfl⟩
    refine Or.inr ⟨⟨projection b.val,⟨b.val,b.property,rfl⟩⟩,⟨projection u.val,hu⟩,?_⟩
    simpa only [map_mul] using congrArg (projection (F:=F)) he

abbrev Points := PSL (F:=F) ⧸ projectiveBorel (F:=F)

theorem projectiveBorel_isCoatom : IsCoatom (projectiveBorel (F:=F)) :=
  CFSGRankOneCosetAction.isCoatom _ (projectiveRoot (F:=F)) projectiveWeyl
    projectiveRoot_le_borel projectiveWeyl_not_mem_borel two_cells

theorem cosetAction_doubly_transitive :
    MulAction.IsMultiplyPretransitive (PSL (F:=F)) (Points (F:=F)) 2 :=
  CFSGRankOneCosetAction.isMultiplyPretransitive_two _ (projectiveRoot (F:=F)) projectiveWeyl
    projectiveRoot_le_borel two_cells

end SymmetricSubgroupAsymptotics.CFSGPSLTwoGeometry
