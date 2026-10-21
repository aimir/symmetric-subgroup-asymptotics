import SymmetricSubgroupAsymptotics.CFSGPSLTwoBorelIntersection
import SymmetricSubgroupAsymptotics.CFSGRankOneSylowAlignment
import SymmetricSubgroupAsymptotics.CFSGRankOneWeylDisplacement

/-! Original U/opposite-U/torus alignment for automorphisms of literal
PSL2. No simplicity or small-field recognition is needed for this geometry. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Pointwise
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoGeometry
open CFSGPSLTwoRootCoordinates
variable {F : Type*} [Field F] [Finite F]

def oppositeRoot : Subgroup (PSL (F:=F)) :=
  (projectiveRoot (F:=F)).map (MulAut.conj (projectiveWeyl (F:=F))).toMonoidHom

theorem opposite_root_normalizer :
    Subgroup.normalizer (oppositeRoot (F:=F) : Set (PSL (F:=F)))=
      (projectiveBorel (F:=F)).map (MulAut.conj (projectiveWeyl (F:=F))).toMonoidHom := by
  rw [←normalizer_projectiveRoot_eq_borel]
  exact (Subgroup.map_normalizer_eq_of_bijective (projectiveRoot (F:=F))
    (MulAut.conj (projectiveWeyl (F:=F))).bijective).symm

theorem pair_normalizer_eq_torus :
    Subgroup.normalizer (projectiveRoot (F:=F) : Set (PSL (F:=F))) ⊓
      Subgroup.normalizer (oppositeRoot (F:=F) : Set (PSL (F:=F)))=pairTorus (F:=F) := by
  rw [normalizer_projectiveRoot_eq_borel,opposite_root_normalizer,
    projectiveBorel_inf_opposite_borel]

theorem map_torus_of_fix_opposite_pair (f : MulAut (PSL (F:=F)))
    (hU : (projectiveRoot (F:=F)).map f.toMonoidHom=projectiveRoot)
    (hO : (oppositeRoot (F:=F)).map f.toMonoidHom=oppositeRoot) :
    (pairTorus (F:=F)).map f.toMonoidHom=pairTorus := by
  rw [←pair_normalizer_eq_torus,Subgroup.map_inf _ _ _ f.injective,
    Subgroup.map_normalizer_eq_of_bijective _ f.bijective,
    Subgroup.map_normalizer_eq_of_bijective _ f.bijective,hU,hO]

theorem exists_inner_fix_opposite_pair (f : MulAut (PSL (F:=F))) :
    ∃ g : PSL (F:=F),
      (projectiveRoot (F:=F)).map (MulAut.conj g*f).toMonoidHom=projectiveRoot ∧
      (oppositeRoot (F:=F)).map (MulAut.conj g*f).toMonoidHom=oppositeRoot ∧
      (pairTorus (F:=F)).map (MulAut.conj g*f).toMonoidHom=pairTorus := by
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨p,hchar,n,hp,_hn⟩ := FiniteField.card' F
  letI : CharP F p := hchar
  letI pslAlignmentPrime : Fact p.Prime := ⟨hp⟩
  let P := projectiveSylow (F:=F) p
  have hP : (P : Subgroup (PSL (F:=F)))=projectiveRoot := projectiveSylow_coe p
  have hBN : projectiveBorel (F:=F)=Subgroup.normalizer (P : Set (PSL (F:=F))) := by
    change projectiveBorel (F:=F)=Subgroup.normalizer
      ((projectiveSylow (F:=F) p : Subgroup (PSL (F:=F))) : Set (PSL (F:=F)))
    rw [projectiveSylow_coe]
    exact normalizer_projectiveRoot_eq_borel.symm
  have hc : ∀ g : PSL (F:=F), g∈projectiveBorel (F:=F) ∨
      ∃ (b : projectiveBorel (F:=F)) (u : P),g=b.val*projectiveWeyl*u.val := by
    intro g
    change g∈projectiveBorel (F:=F) ∨ ∃ (b : projectiveBorel (F:=F))
      (u : (P : Subgroup (PSL (F:=F)))),g=b.val*projectiveWeyl*u.val
    rw [hP]
    exact two_cells g
  obtain ⟨g,hU,hO⟩ := CFSGRankOneSylowAlignment.exists_inner_fix_pair
    P projectiveBorel projectiveWeyl hBN projectiveWeyl_not_mem_borel hc f
  have hU' : (projectiveRoot (F:=F)).map (MulAut.conj g*f).toMonoidHom=projectiveRoot := by
    have hh := congrArg (fun Q : Sylow p (PSL (F:=F)) => Q.toSubgroup) hU
    change (P : Subgroup (PSL (F:=F))).map (MulAut.conj g*f).toMonoidHom=
      (P : Subgroup (PSL (F:=F))) at hh
    rwa [hP] at hh
  have hO' : (oppositeRoot (F:=F)).map (MulAut.conj g*f).toMonoidHom=oppositeRoot := by
    have hh := congrArg (fun Q : Sylow p (PSL (F:=F)) => Q.toSubgroup) hO
    change ((P : Subgroup (PSL (F:=F))).map
      (MulAut.conj (projectiveWeyl (F:=F))).toMonoidHom).map
        (MulAut.conj g*f).toMonoidHom=
          (P : Subgroup (PSL (F:=F))).map
            (MulAut.conj (projectiveWeyl (F:=F))).toMonoidHom at hh
    rw [hP] at hh
    exact hh
  exact ⟨g,hU',hO',map_torus_of_fix_opposite_pair _ hU' hO'⟩

theorem weyl_displacement_mem_torus (f : MulAut (PSL (F:=F)))
    (hU : (projectiveRoot (F:=F)).map f.toMonoidHom=projectiveRoot)
    (hO : (oppositeRoot (F:=F)).map f.toMonoidHom=oppositeRoot) :
    f projectiveWeyl*(projectiveWeyl (F:=F))⁻¹∈pairTorus (F:=F) := by
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨p,hchar,n,hp,_hn⟩ := FiniteField.card' F
  letI : CharP F p := hchar
  letI pslDisplacementPrime : Fact p.Prime := ⟨hp⟩
  let P := projectiveSylow (F:=F) p
  have hP : (P : Subgroup (PSL (F:=F)))=projectiveRoot := projectiveSylow_coe p
  have hfP : f • P=P := by
    apply Sylow.ext
    change (P : Subgroup (PSL (F:=F))).map f.toMonoidHom=(P : Subgroup (PSL (F:=F)))
    rwa [hP]
  have hfO : f • ((projectiveWeyl (F:=F)) • P)=(projectiveWeyl (F:=F)) • P := by
    apply Sylow.ext
    change ((P : Subgroup (PSL (F:=F))).map
      (MulAut.conj (projectiveWeyl (F:=F))).toMonoidHom).map f.toMonoidHom=
        (P : Subgroup (PSL (F:=F))).map
          (MulAut.conj (projectiveWeyl (F:=F))).toMonoidHom
    rw [hP]
    exact hO
  have hw : (projectiveWeyl (F:=F))⁻¹=projectiveWeyl :=
    inv_eq_of_mul_eq_one_right projectiveWeyl_square
  have hh := CFSGRankOneWeylDisplacement.mem_pair_normalizer P projectiveWeyl hw f hfP hfO
  change f projectiveWeyl*(projectiveWeyl (F:=F))⁻¹∈
    Subgroup.normalizer ((P : Subgroup (PSL (F:=F))) : Set (PSL (F:=F))) ⊓
      Subgroup.normalizer (((P : Subgroup (PSL (F:=F))).map
        (MulAut.conj (projectiveWeyl (F:=F))).toMonoidHom) : Set (PSL (F:=F))) at hh
  rw [hP] at hh
  rw [←pair_normalizer_eq_torus]
  exact hh

end SymmetricSubgroupAsymptotics.CFSGPSLTwoGeometry
