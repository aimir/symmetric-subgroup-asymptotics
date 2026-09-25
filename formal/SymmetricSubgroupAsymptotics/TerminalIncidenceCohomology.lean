import SymmetricSubgroupAsymptotics.TerminalCohomology
import SymmetricSubgroupAsymptotics.QuadraticIncidence

/-!
# The actual inflation kernel and terminal quadratic tests

Diagonal evaluation descends to actual binary group cohomology. Its image
on the retained inflation kernel is an actual allowable function subspace.
For bilinear cocycles, splitting after pullback to a binary kernel times an
arbitrary exterior forces the full diagonal to lie in that subspace. The
proof uses diagonal and commuting-pair evaluations, without assuming a
Künneth decomposition or injectivity of inflation.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics

variable {A U : Type} [AddCommGroup A] [Module (ZMod 2) A]
  [AddCommGroup U] [Module (ZMod 2) U]

private theorem terminal_binary_add_self (a : A) : a+a=0 := by
  have h : (2 : ZMod 2) • a = 0 := by
    rw [show (2 : ZMod 2) = 0 by decide, zero_smul]
  simpa only [← one_add_one_eq_two, add_smul, one_smul] using h

/-- Diagonal evaluation with its normalization correction; arbitrary
cocycle representatives, not only normalized representatives, are accepted. -/
def terminalCocycleDiagonal :
    groupCohomology.cocycles₂ (Rep.trivial (ZMod 2) (Multiplicative A) (ZMod 2)) →ₗ[ZMod 2]
      (A → ZMod 2) where
  toFun c a := c (Multiplicative.ofAdd a,Multiplicative.ofAdd a) - c (1,1)
  map_add' c d := by
    ext a
    change (c (Multiplicative.ofAdd a,Multiplicative.ofAdd a)+d (Multiplicative.ofAdd a,Multiplicative.ofAdd a))-
      (c (1,1)+d (1,1))=(c (Multiplicative.ofAdd a,Multiplicative.ofAdd a)-c (1,1))+
      (d (Multiplicative.ofAdd a,Multiplicative.ofAdd a)-d (1,1))
    abel
  map_smul' s c := by
    ext a
    change s*c (Multiplicative.ofAdd a,Multiplicative.ofAdd a)-s*c (1,1)=
      s*(c (Multiplicative.ofAdd a,Multiplicative.ofAdd a)-c (1,1))
    ring

private theorem terminalCocycleDiagonal_ker :
    (groupCohomology.H2π (Rep.trivial (ZMod 2) (Multiplicative A) (ZMod 2))).hom.ker ≤
      (terminalCocycleDiagonal (A := A)).ker := by
  intro c hc
  obtain ⟨b,hb⟩ := (groupCohomology.H2π_eq_zero_iff c).mp hc
  apply funext
  intro a
  have h1 := congrFun hb (Multiplicative.ofAdd a,Multiplicative.ofAdd a)
  have h0 := congrFun hb (1,1)
  change b (Multiplicative.ofAdd a) - b (Multiplicative.ofAdd (a+a)) +
    b (Multiplicative.ofAdd a) = c (Multiplicative.ofAdd a,Multiplicative.ofAdd a) at h1
  change b 1 - b (1*1) + b 1 = c (1,1) at h0
  change c (Multiplicative.ofAdd a,Multiplicative.ofAdd a) - c (1,1) = 0
  rw [← h1, ← h0, terminal_binary_add_self]
  simp only [mul_one]
  change b (Multiplicative.ofAdd a) - b 1 + b (Multiplicative.ofAdd a) - (b 1-b 1+b 1)=0
  have ha := CharTwo.add_self_eq_zero (b (Multiplicative.ofAdd a))
  have hz := CharTwo.add_self_eq_zero (b 1)
  linear_combination ha - hz

omit [Module (ZMod 2) A] in
private theorem terminalH2Projection_surjective :
    Function.Surjective (groupCohomology.H2π
      (Rep.trivial (ZMod 2) (Multiplicative A) (ZMod 2))).hom :=
  (ModuleCat.epi_iff_surjective _).mp inferInstance

/-- A well-defined linear invariant of actual H² classes. -/
def terminalH2Diagonal :
    groupCohomology.H2 (Rep.trivial (ZMod 2) (Multiplicative A) (ZMod 2)) →ₗ[ZMod 2]
      (A → ZMod 2) :=
  let p := (groupCohomology.H2π
    (Rep.trivial (ZMod 2) (Multiplicative A) (ZMod 2))).hom
  (p.ker.liftQ terminalCocycleDiagonal terminalCocycleDiagonal_ker).comp
    (p.quotKerEquivOfSurjective terminalH2Projection_surjective).symm.toLinearMap

@[simp] theorem terminalH2Diagonal_class
    (c : groupCohomology.cocycles₂ (Rep.trivial (ZMod 2) (Multiplicative A) (ZMod 2))) :
    terminalH2Diagonal (groupCohomology.H2π _ c) = terminalCocycleDiagonal c := by
  unfold terminalH2Diagonal
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

/-- The original retained inflation kernel, followed by diagonal evaluation
and pullback along the exterior coordinate. It is a subspace of literal
functions on the entire binary record domain. -/
def terminalAllowedDiagonals {T : Type} [Group T]
    (β : T →* Multiplicative A) : Submodule (ZMod 2) (U × A → ZMod 2) :=
  ((binaryH2Pullback β).ker).map
    ((LinearMap.funLeft (ZMod 2) (ZMod 2) (Prod.snd : U × A → A)).comp
      (terminalH2Diagonal (A := A)))

omit [AddCommGroup U] [Module (ZMod 2) U] in
/-- The retained allowed space costs at most the dimension of the actual
inflation kernel. No equality of different annihilators is used. -/
theorem terminalAllowedDiagonals_finrank_le {T : Type} [Group T] [Finite A]
    (β : T →* Multiplicative A) :
    Module.finrank (ZMod 2) (terminalAllowedDiagonals (U := U) β) ≤
      Module.finrank (ZMod 2) (binaryH2Pullback β).ker := by
  letI : Finite (groupCohomology.H2
      (Rep.trivial (ZMod 2) (Multiplicative A) (ZMod 2))) :=
    Finite.of_surjective _ terminalH2Projection_surjective
  exact Submodule.finrank_map_le _ _

/-- A literal bilinear cocycle on a binary vector space. Its diagonal is
the corresponding quadratic function, including its square terms. -/
def terminalBilinearCocycle (c : LinearMap.BilinForm (ZMod 2) A) :
    groupCohomology.cocycles₂ (Rep.trivial (ZMod 2) (Multiplicative A) (ZMod 2)) :=
  ⟨fun xy => c xy.1.toAdd xy.2.toAdd, by
    apply (groupCohomology.mem_cocycles₂_iff _).mpr
    intro x y z
    change c (x.toAdd+y.toAdd) z.toAdd + c x.toAdd y.toAdd =
      c y.toAdd z.toAdd + c x.toAdd (y.toAdd+z.toAdd)
    simp only [map_add, LinearMap.add_apply]
    abel⟩

@[simp] theorem terminalH2Diagonal_bilinear (c : LinearMap.BilinForm (ZMod 2) A) :
    terminalH2Diagonal (groupCohomology.H2π _ (terminalBilinearCocycle c)) =
      fun a => c a a := by
  rw [terminalH2Diagonal_class]
  ext a
  change c a a - c 0 0 = c a a
  simp

/-- Pullback from the actual product of the binary vertical kernel and the
complete exterior. The exterior is not assumed abelian. -/
def terminalProductQuotient {T : Type} [Group T] (β : T →* Multiplicative A) :
    Multiplicative U × T →* Multiplicative (U × A) where
  toFun x := Multiplicative.ofAdd (x.1.toAdd,(β x.2).toAdd)
  map_one' := by simp
  map_mul' x y := by simp [map_mul]; rfl

/-- Necessary vertical, mixed, and retained exterior tests, proved directly
from an actual coboundary on `U × T`. These are exactly the three tests
needed for the positive terminal incidence relaxation. -/
theorem terminal_bilinear_splitting_tests {T : Type} [Group T]
    (β : T →* Multiplicative A) (hβ : Function.Surjective β)
    (c : LinearMap.BilinForm (ZMod 2) (U × A))
    (h : groupCohomology.H2π _
      (binaryCocyclePullback (terminalProductQuotient (U := U) β)
        (terminalBilinearCocycle c)) = 0) :
    (∀ u, c (u,0) (u,0)=0) ∧
      (∀ u a, c (u,0) (0,a) + c (0,a) (u,0)=0) ∧
      groupCohomology.H2π _
        (terminalBilinearCocycle (c.compl₁₂ (LinearMap.inr _ _ _) (LinearMap.inr _ _ _))) ∈
          (binaryH2Pullback β).ker := by
  obtain ⟨b,hb⟩ := (groupCohomology.H2π_eq_zero_iff _).mp h
  have he (x y : Multiplicative U × T) :
      c (x.1.toAdd,(β x.2).toAdd) (y.1.toAdd,(β y.2).toAdd) = b y - b (x*y) + b x :=
    (congrFun hb (x,y)).symm
  have hb0 : b 1=0 := by
    have he0 := he 1 1
    simp only [Prod.fst_one, Prod.snd_one, map_one, toAdd_one] at he0
    change c (0 : U × A) 0 = b 1 - b (1*1) + b 1 at he0
    simpa using he0.symm
  refine ⟨?_,?_,?_⟩
  · intro u
    have hu := he (Multiplicative.ofAdd u,1) (Multiplicative.ofAdd u,1)
    have hs : (Multiplicative.ofAdd u,(1:T)) * (Multiplicative.ofAdd u,1) = 1 := by
      apply Prod.ext
      · change Multiplicative.ofAdd (u+u) = (1 : Multiplicative U)
        rw [terminal_binary_add_self]
        rfl
      · simp
    simpa only [map_one, toAdd_one, hs, hb0, sub_zero,
      CharTwo.add_self_eq_zero] using hu
  · intro u a
    obtain ⟨t,ht⟩ := hβ (Multiplicative.ofAdd a)
    have hxy := he (Multiplicative.ofAdd u,1) (1,t)
    have hyx := he (1,t) (Multiplicative.ofAdd u,1)
    have hcomm : (Multiplicative.ofAdd u,(1:T)) * (1,t) =
        (1,t) * (Multiplicative.ofAdd u,1) := by simp
    simp only [map_one, toAdd_one, ht,
      toAdd_ofAdd, hcomm] at hxy hyx
    have hsame : c (u,0) (0,a) = c (0,a) (u,0) := by
      rw [hxy,hyx]
      abel
    rw [hsame, CharTwo.add_self_eq_zero]
  · rw [LinearMap.mem_ker, binaryH2Pullback_class, groupCohomology.H2π_eq_zero_iff]
    refine ⟨fun t => b (1,t), funext fun xy => ?_⟩
    have he' := he (1,xy.1) (1,xy.2)
    change b (1,xy.2) - b (1,xy.1*xy.2) + b (1,xy.1) =
      c (0,(β xy.1).toAdd) (0,(β xy.2).toAdd)
    simpa only [Prod.mk_mul_mk,one_mul] using he'.symm

/-- Splitting forces the entire quadratic outcome into the image of the
actual retained inflation kernel, including the mixed and vertical tests. -/
theorem terminal_bilinear_diagonal_mem_allowed {T : Type} [Group T]
    (β : T →* Multiplicative A) (hβ : Function.Surjective β)
    (c : LinearMap.BilinForm (ZMod 2) (U × A))
    (h : groupCohomology.H2π _
      (binaryCocyclePullback (terminalProductQuotient (U := U) β)
        (terminalBilinearCocycle c)) = 0) :
    (fun x : U × A => c x x) ∈ terminalAllowedDiagonals β := by
  obtain ⟨hu,hm,ha⟩ := terminal_bilinear_splitting_tests β hβ c h
  refine Submodule.mem_map.mpr ⟨_,ha,?_⟩
  rw [LinearMap.comp_apply,terminalH2Diagonal_bilinear]
  ext x
  change c (0,x.2) (0,x.2) = c x x
  have hx : x = (x.1,0)+(0,x.2) := by simp
  conv_rhs => rw [hx]
  simp only [map_add, LinearMap.add_apply]
  have hu' := hu x.1
  have hm' := hm x.1 x.2
  linear_combination -hu' - hm'

end SymmetricSubgroupAsymptotics
