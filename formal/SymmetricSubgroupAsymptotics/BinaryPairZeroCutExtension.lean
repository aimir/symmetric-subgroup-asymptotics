import SymmetricSubgroupAsymptotics.BinaryPairPrefixChart

/-! The zero-cut extension attached to an arbitrary original pair frame
and normal subgroup. The quotient, its kernel, and its conjugation action
are constructed from those actual objects. No finite local certificate,
faithful quotient action, or splitting is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U I) (N : Subgroup U) [N.Normal]

/-- The literal zero central cut, with the quotient action retained. -/
def zeroCutModule : Rep (ZMod 2) (U ⧸ (F.top.ker⊔N)) :=
  Rep.of (F.cutRepresentation N ⊥ bot_le)

def zeroCutMap : F.top.ker →* Multiplicative (F.zeroCutModule N) :=
  normalSectionCutMap F.top.ker (F.sectionMap N) ⊥

theorem zeroCutMap_surjective : Function.Surjective (F.zeroCutMap N) :=
  normalSectionCutMap_surjective F.top.ker (F.sectionMap N) (F.sectionMap_surjective N) ⊥

theorem zeroCutMap_ker : (F.zeroCutMap N).ker=N.subgroupOf F.top.ker := by
  ext l
  rw [MonoidHom.mem_ker]
  change normalSectionCutMap F.top.ker (F.sectionMap N) ⊥ l=1 ↔ (l:U)∈N
  rw [← MonoidHom.mem_ker,normalSectionCutMap_ker,Submodule.mem_bot]
  change F.sectionMap N l=1 ↔ (l:U)∈N
  rw [← MonoidHom.mem_ker,F.sectionMap_ker N]
  rfl

@[simp] theorem zeroCutModule_apply (u : U) (l : F.top.ker) :
    (F.zeroCutModule N).ρ (QuotientGroup.mk' (F.top.ker⊔N) u)
      (F.zeroCutMap N l).toAdd=
        (F.zeroCutMap N (MulAut.conjNormal u l)).toAdd :=
  normalSectionCutRepresentation_apply F.top.ker N (F.sectionMap N)
    (F.sectionMap_surjective N) (F.sectionMap_ker N) ⊥ bot_le u l

instance zeroCutModule_finite [Finite I] : Finite (F.zeroCutModule N) := by
  letI : Finite (F.kernelSpace ⧸ F.normalSpace N) :=
    Finite.of_surjective (F.normalSpace N).mkQ (F.normalSpace N).mkQ_surjective
  exact Finite.of_surjective
    (⊥ : Submodule (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N)).mkQ
    (⊥ : Submodule (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N)).mkQ_surjective

/-- The original normal quotient maps onto the original acting top. -/
def zeroCutBase : (U ⧸ N) →* U ⧸ (F.top.ker⊔N) :=
  QuotientGroup.lift N (QuotientGroup.mk' (F.top.ker⊔N)) (by
    rw [QuotientGroup.ker_mk']; exact le_sup_right)

@[simp] theorem zeroCutBase_apply (u : U) :
    F.zeroCutBase N (QuotientGroup.mk' N u)=QuotientGroup.mk' (F.top.ker⊔N) u := rfl

theorem zeroCutBase_surjective : Function.Surjective (F.zeroCutBase N) := by
  intro b
  obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (F.top.ker⊔N) b
  exact ⟨QuotientGroup.mk' N u,rfl⟩

def zeroCutKernelMap : F.top.ker →* (F.zeroCutBase N).ker where
  toFun l := ⟨QuotientGroup.mk' N (l:U),by
    rw [MonoidHom.mem_ker,F.zeroCutBase_apply]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_sup_left l.property)⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' a b := by apply Subtype.ext; exact map_mul _ _ _

theorem zeroCutKernelMap_surjective : Function.Surjective (F.zeroCutKernelMap N) := by
  intro q
  obtain ⟨u,hu⟩ := QuotientGroup.mk'_surjective N q.val
  have hub : QuotientGroup.mk' (F.top.ker⊔N) u=1 := by
    rw [← F.zeroCutBase_apply N u,hu]
    exact q.property
  obtain ⟨l,hl,n,hn,hln⟩ := Subgroup.mem_sup_of_normal_right.mp
    ((QuotientGroup.eq_one_iff _).mp hub)
  refine ⟨⟨l,hl⟩,?_⟩
  apply Subtype.ext
  change QuotientGroup.mk' N l=q.val
  rw [← hu,← hln,map_mul]
  have hnq : QuotientGroup.mk' N n=1 := (QuotientGroup.eq_one_iff _).mpr hn
  rw [hnq,mul_one]

theorem zeroCutKernelMap_ker : (F.zeroCutKernelMap N).ker=N.subgroupOf F.top.ker := by
  ext l
  rw [MonoidHom.mem_ker,Subtype.ext_iff]
  change QuotientGroup.mk' N (l:U)=1 ↔ (l:U)∈N
  exact QuotientGroup.eq_one_iff _

def zeroCutKernelEquiv : Multiplicative (F.zeroCutModule N) ≃* (F.zeroCutBase N).ker :=
  binaryPair_sameKernelEquiv (F.zeroCutMap N) (F.zeroCutKernelMap N)
    (F.zeroCutMap_surjective N) (F.zeroCutKernelMap_surjective N)
    ((F.zeroCutMap_ker N).trans (F.zeroCutKernelMap_ker N).symm)

@[simp] theorem zeroCutKernelEquiv_apply (l : F.top.ker) :
    F.zeroCutKernelEquiv N (F.zeroCutMap N l)=F.zeroCutKernelMap N l :=
  binaryPair_sameKernelEquiv_apply _ _ _ _ _ l

/-- The original nonsplit extension has this exact zero-cut module
as its kernel, with every original conjugation respected. -/
def zeroCutModuleChart : OriginalKernelModuleChart (F.zeroCutBase N) (F.zeroCutModule N) where
  equiv := F.zeroCutKernelEquiv N
  conjugate q a := by
    obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective N q
    obtain ⟨l,hl⟩ := F.zeroCutMap_surjective N (Multiplicative.ofAdd a)
    have ha : (F.zeroCutMap N l).toAdd=a := congrArg Multiplicative.toAdd hl
    rw [← ha,F.zeroCutBase_apply,F.zeroCutModule_apply]
    have he (m : F.top.ker) :
        (F.zeroCutKernelEquiv N (F.zeroCutMap N m) : U ⧸ N)=
          QuotientGroup.mk' N (m:U) :=
      congrArg Subtype.val (F.zeroCutKernelEquiv_apply N m)
    calc
      _ = QuotientGroup.mk' N (MulAut.conjNormal u l : U) := he (MulAut.conjNormal u l)
      _ = QuotientGroup.mk' N u * QuotientGroup.mk' N (l:U) *
          (QuotientGroup.mk' N u)⁻¹ := by
        change QuotientGroup.mk' N (u*(l:U)*u⁻¹)=_
        simp only [map_mul,map_inv]
      _ = _ := congrArg (fun z : U ⧸ N =>
        QuotientGroup.mk' N u*z*(QuotientGroup.mk' N u)⁻¹) (he l).symm

end SymmetricSubgroupAsymptotics.BinaryPairFrame
