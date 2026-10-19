import SymmetricSubgroupAsymptotics.MarkedC4FiniteBinaryWordTargets
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Graph FIRST, then literal physical annihilators.
All C4^r coordinates stay in ONE global mark group M. The physical
intersection in each factor is intersected with the actual character kernel
before quotienting; no character descent through the old intersections is
assumed. The selected normal subgroups belong to fixed physical menus. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.OriginalGraphAnnihilators
open FiniteOrbitWordShapes FiniteBinaryWordTargets

variable {C b : ℕ} (T : Target C b) {M : Type} [Group M]
  (f : T.image →* M)
abbrev Ambient := Product T.letters

def graphHom : T.image →* (Ambient T × M) where
  toFun h := (h.val,f h)
  map_one' := by simp
  map_mul' _ _ := by simp

def graph : Subgroup (Ambient T × M) := (graphHom T f).range

def unmarked : Ambient T →* (Ambient T × M) where
  toFun v := (v,1)
  map_one' := rfl
  map_mul' _ _ := by simp

/-- Actual physical elements whose mark restriction is identically one. -/
def annihilator : Subgroup (Ambient T) := (graph T f).comap (unmarked T)

/-- The SAME graph's actual isolated-factor intersections. -/
def factor (i : Fin T.shape.length.val) : Subgroup (T.letters i) :=
  (annihilator T f).comap (MonoidHom.mulSingle (fun j => T.letters j) i)

/-- Physical subdirectness proves ambient Gi-normality even though the
whole original subgroup need not be normal in the physical product. -/
theorem factor_normal (i : Fin T.shape.length.val) : (factor T f i).Normal := by
  refine ⟨?_⟩
  intro n hn g
  obtain ⟨h,hg⟩ := T.subdirect i g
  have hx : graphHom T f h ∈ graph T f := ⟨h,rfl⟩
  have hn' : (Pi.mulSingle i n,1) ∈ graph T f := hn
  have hc := (graph T f).mul_mem ((graph T f).mul_mem hx hn') ((graph T f).inv_mem hx)
  have he : graphHom T f h*(Pi.mulSingle i n,1)*(graphHom T f h)⁻¹=
      (Pi.mulSingle i (g*n*g⁻¹),1) := by
    apply Prod.ext
    · funext j
      by_cases hji : j=i
      · subst j
        simpa [graphHom] using
          congrArg (fun x : T.letters i => x*n*x⁻¹) hg
      · simp [graphHom,Pi.mulSingle,hji,Ne.symm hji]
    · simp [graphHom]
  change (Pi.mulSingle i (g*n*g⁻¹),1) ∈ graph T f
  exact he ▸ hc

local instance factorNormal (i : Fin T.shape.length.val) : (factor T f i).Normal :=
  factor_normal T f i

def physicalProduct : Subgroup (Ambient T) := Subgroup.pi Set.univ (factor T f)

/-- Finite products of the isolated intersections lie in the SAME graph
annihilator, including every shared-character correlation. -/
theorem product_le_annihilator : physicalProduct T f ≤ annihilator T f := by
  apply Subgroup.pi_le_iff.mpr
  intro i
  exact Subgroup.map_comap_le (MonoidHom.mulSingle (fun j => T.letters j) i)
    (annihilator T f)

instance physicalProduct_normal : (physicalProduct T f).Normal := by
  refine ⟨?_⟩
  intro n hn g i _
  exact (factor_normal T f i).conj_mem (n i) (hn i (Set.mem_univ i)) (g i)

/-- Vanishing is DERIVED for the actual retained product; it is not assumed
for the unmarked physical intersections. -/
theorem vanishes (h : T.image) (hh : h.val ∈ physicalProduct T f) : f h=1 := by
  have ha := product_le_annihilator T f hh
  change (h.val,1) ∈ (graphHom T f).range at ha
  obtain ⟨k,hk⟩ := ha
  have hkh : k=h := Subtype.ext (congrArg Prod.fst hk)
  have hm := congrArg Prod.snd hk
  change f k=1 at hm
  simpa only [hkh] using hm

/-- Only physical coordinates are quotiented. The single global mark group
is retained verbatim. -/
def quotientMap : (Ambient T × M) →* ((Ambient T ⧸ physicalProduct T f) × M) :=
  (QuotientGroup.mk' (physicalProduct T f)).prodMap (MonoidHom.id M)

def quotientGraph : Subgroup ((Ambient T ⧸ physicalProduct T f) × M) :=
  (graph T f).map (quotientMap T f)

theorem quotient_kernel_le_graph : (quotientMap T f).ker ≤ graph T f := by
  intro z hz
  have he := MonoidHom.mem_ker.mp hz
  have hp : z.1 ∈ physicalProduct T f := by
    apply (QuotientGroup.eq_one_iff (N := physicalProduct T f) z.1).mp
    exact congrArg Prod.fst he
  have hm : z.2=1 := congrArg Prod.snd he
  have ha := product_le_annihilator T f hp
  change (z.1,1) ∈ graph T f at ha
  have hz : (z.1,1)=z := Prod.ext rfl hm.symm
  exact hz ▸ ha

/-- The quotient graph and the selected physical annihilator menu recover
its ORIGINAL character graph exactly. This is the legitimate descent. -/
theorem recover_graph : (quotientGraph T f).comap (quotientMap T f)=graph T f :=
  Subgroup.comap_map_eq_self (quotient_kernel_le_graph T f)

end SymmetricSubgroupAsymptotics.MarkedC4.OriginalGraphAnnihilators
