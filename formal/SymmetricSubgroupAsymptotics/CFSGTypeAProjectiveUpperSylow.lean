import SymmetricSubgroupAsymptotics.CFSGTypeAProjectiveUpperCenter
import SymmetricSubgroupAsymptotics.CFSGTypeAGoodSylow

/-! The actual defining-characteristic projective upper Sylow, together
with the exact original U parameter equivalence. Its centre is transported
through an injective restriction of the original central quotient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeAProjectiveUpperCenter
open Matrix CFSGUpperUnitriangular CFSGTypeAElementaryMatrices
variable {F : Type*} [Field F] [Finite F] {n : ℕ}

def projectiveUpperSylow (p : ℕ) [Fact p.Prime] [CharP F p] :
    Sylow p (PSL (F:=F) (n:=n)) :=
  (CFSGTypeAGoodSylow.actualUpperSylow F p n).mapSurjective
    (f:=projection) (QuotientGroup.mk'_surjective _)

theorem projectiveUpperSylow_coe (p : ℕ) [Fact p.Prime] [CharP F p] :
    (projectiveUpperSylow (F:=F) (n:=n) p : Subgroup (PSL (F:=F) (n:=n)))=
      projectiveUpper (F:=F) (n:=n) := by
  change (upperUnitriangular F n).map projection=
    (projection.comp (upperUnitriangular F n).subtype).range
  rw [MonoidHom.range_comp,Subgroup.range_subtype]

def upperSylowEquiv (p : ℕ) [Fact p.Prime] [CharP F p] (hn : 1≤n) :
    upperUnitriangular F n≃*projectiveUpperSylow (F:=F) (n:=n) p :=
  (upperEquiv hn).trans (MulEquiv.subgroupCongr (projectiveUpperSylow_coe p).symm)

theorem upperSylowEquiv_val (p : ℕ) [Fact p.Prime] [CharP F p] (hn : 1≤n)
    (u : upperUnitriangular F n) :
    ((upperSylowEquiv p hn u : projectiveUpperSylow (F:=F) (n:=n) p) : PSL (F:=F) (n:=n))=
      projection u.val := rfl

theorem projectiveUpperSylow_center_highestRoot (p : ℕ) [Fact p.Prime] [CharP F p]
    (hn : 2≤n) (z : projectiveUpperSylow (F:=F) (n:=n) p)
    (hz : z∈Subgroup.center (projectiveUpperSylow (F:=F) (n:=n) p)) :
    ∃a : F,(z : PSL (F:=F) (n:=n))=
      projection (elementary (show (⟨0,by omega⟩ : Fin n)≠⟨n-1,by omega⟩ by
        intro he;have hh := congrArg Fin.val he;dsimp only at hh;omega) a) := by
  let e := upperSylowEquiv (F:=F) (n:=n) p (by omega : 1≤n)
  let u := e.symm z
  have hu : u∈Subgroup.center (upperUnitriangular F n) :=
    ((Subgroup.centerCongr e).symm ⟨z,hz⟩).property
  obtain ⟨a,ha⟩ := center_upperUnitriangular_eq_highestRoot hn u hu
  refine ⟨a,?_⟩
  have he := congrArg (fun t : projectiveUpperSylow (F:=F) (n:=n) p =>
    (t : PSL (F:=F) (n:=n))) (e.apply_symm_apply z)
  change projection u.val=(z : PSL (F:=F) (n:=n)) at he
  rw [←he,ha]

theorem highestRoot_projectiveUpperSylow_center (p : ℕ) [Fact p.Prime] [CharP F p]
    (hn : 2≤n) (a : F) :
    ∃z : projectiveUpperSylow (F:=F) (n:=n) p,
      z∈Subgroup.center (projectiveUpperSylow (F:=F) (n:=n) p) ∧
      (z : PSL (F:=F) (n:=n))=
        projection (elementary (show (⟨0,by omega⟩ : Fin n)≠⟨n-1,by omega⟩ by
          intro he;have hh := congrArg Fin.val he;dsimp only at hh;omega) a) := by
  let u : upperUnitriangular F n :=
    ⟨elementary (show (⟨0,by omega⟩ : Fin n)≠⟨n-1,by omega⟩ by
      intro he;have hh := congrArg Fin.val he;dsimp only at hh;omega) a,
      elementary_mem_upperUnitriangular (show (⟨0,by omega⟩ : Fin n)<⟨n-1,by omega⟩ by
        change 0 < n-1;omega) a⟩
  let e := upperSylowEquiv (F:=F) (n:=n) p (by omega : 1≤n)
  refine ⟨e u,?_,rfl⟩
  exact (Subgroup.centerCongr e
    ⟨u,highestRoot_mem_center_upperUnitriangular hn a⟩).property

end SymmetricSubgroupAsymptotics.CFSGTypeAProjectiveUpperCenter
