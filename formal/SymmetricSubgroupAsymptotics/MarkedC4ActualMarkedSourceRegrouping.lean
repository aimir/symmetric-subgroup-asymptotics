import SymmetricSubgroupAsymptotics.MarkedC4ActualGlobalMarkGeneratorRank

/-! The ONE global marker is placed on the R-side of the ordinary RDT4.6
source geometry. The independent physical tail remains the P-side. All
groups below are actual images of the same original marked subgroup. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualMarkedSourceRegrouping

variable {B P M : Type} [Group B] [Group P] [Group M]
  (A : Subgroup ((B × P) × M))

def left : A →* B × M where
  toFun a := (a.val.1.1,a.val.2)
  map_one' := rfl
  map_mul' _ _ := rfl

def tail : A →* P where
  toFun a := a.val.1.2
  map_one' := rfl
  map_mul' _ _ := rfl

abbrev LeftImage := (left A).range

def regroup : A →* LeftImage A × P :=
  (left A).rangeRestrict.prod (tail A)

theorem regroup_injective : Function.Injective (regroup A) := by
  intro x y h
  have hb := congrArg (fun z : LeftImage A × P => z.1.val.1) h
  have hm := congrArg (fun z : LeftImage A × P => z.1.val.2) h
  have hp := congrArg (fun z : LeftImage A × P => z.2) h
  change x.val.1.1=y.val.1.1 at hb
  change x.val.2=y.val.2 at hm
  change x.val.1.2=y.val.1.2 at hp
  apply Subtype.ext
  apply Prod.ext
  · exact Prod.ext hb hp
  · exact hm

abbrev Source := (regroup A).range

def sourceEquiv : A ≃* Source A := MonoidHom.ofInjective (regroup_injective A)

def sourceTail : Source A →* P :=
  (MonoidHom.snd (LeftImage A) P).comp (Source A).subtype

/-- Exactly the original independent-tail surjectivity, with no condition
on the global marker projection. -/
theorem sourceTail_surjective (h : Function.Surjective (tail A)) :
    Function.Surjective (sourceTail A) := by
  intro p
  obtain ⟨a,ha⟩ := h p
  exact ⟨⟨regroup A a,⟨a,rfl⟩⟩,ha⟩

theorem sourceLeft_surjective : Function.Surjective
    ((MonoidHom.fst (LeftImage A) P).comp (Source A).subtype) := by
  intro l
  obtain ⟨a,ha⟩ := (left A).rangeRestrict_surjective l
  exact ⟨⟨regroup A a,⟨a,rfl⟩⟩,ha⟩

theorem tail_commutes (a : A) :
    sourceTail A (sourceEquiv A a)=tail A a := rfl

end SymmetricSubgroupAsymptotics.MarkedC4.ActualMarkedSourceRegrouping
