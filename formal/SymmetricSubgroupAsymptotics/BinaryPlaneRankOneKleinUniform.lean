import SymmetricSubgroupAsymptotics.BinaryPlaneRankOneCommutingInvolution
import SymmetricSubgroupAsymptotics.BinaryCubicTwoOrbitPolynomialUniform

/-! Uniform binary generation for the ACTUAL rank-one odd-kernel class
with regular V4 block image. Reindexing the two involution orbits is the
only point chart; actual local transport maps remain unrestricted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryPlaneRankOneKleinUniform
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open BinaryPlaneWreathActualOddKernel
open RankOneCubicSylowCentralizer (Cubic Blocks)
open BinaryCubicTwoOrbitPolynomialUniform (Index flip)

local instance : Fintype Blocks := BinaryRegularKleinWreath.rFintype
local instance : DecidableEq Blocks := BinaryRegularKleinWreath.rDecidableEq

private def orbitFunction (r : Blocks) (i : Index) : Blocks :=
  (if r=BinaryRegularKleinWreath.a then BinaryRegularKleinWreath.b
    else BinaryRegularKleinWreath.a)^i.1.val*r^i.2.val

private theorem orbitFunction_bijective : ∀ r : Blocks, r≠1 →
    Function.Bijective (orbitFunction r) := by decide +kernel

private def orbitChart (r : Blocks) (hr : r≠1) : Index ≃ Blocks :=
  Equiv.ofBijective (orbitFunction r) (orbitFunction_bijective r hr)

private theorem orbitChart_flip (r : Blocks) (hr : r≠1) (i : Index) :
    orbitChart r hr (flip i)=r*orbitChart r hr i := by
  change orbitFunction r (flip i)=r*orbitFunction r i
  exact (by decide +kernel : ∀ r : Blocks, r≠1 → ∀ i : Index,
    orbitFunction r (flip i)=r*orbitFunction r i) r hr i

private def coordinateEquiv (r : Blocks) (hr : r≠1) :
    (Blocks → Plane) ≃ₗ[ZMod 2] (Index → Plane) :=
  LinearEquiv.funCongrLeft (ZMod 2) Plane (orbitChart r hr)

private theorem coordinateEquiv_symm_single (r : Blocks) (hr : r≠1)
    (i : Index) (v : Plane) :
    (coordinateEquiv r hr).symm (Pi.single i v)=Pi.single (orbitChart r hr i) v := by
  funext j
  change (Pi.single i v : Index → Plane) ((orbitChart r hr).symm j)=
    (Pi.single (orbitChart r hr i) v : Blocks → Plane) j
  by_cases hj : j=orbitChart r hr i
  · subst j
    rw [(orbitChart r hr).symm_apply_apply i]
    simp only [Pi.single_eq_same]
  · have hn : (orbitChart r hr).symm j≠i := by
      intro h
      apply hj
      exact ((orbitChart r hr).apply_symm_apply j).symm.trans
        (congrArg (orbitChart r hr) h)
    rw [Pi.single_eq_of_ne hn,Pi.single_eq_of_ne hj]

private theorem coordinateEquiv_single (r : Blocks) (hr : r≠1)
    (j : Blocks) (v : Plane) :
    coordinateEquiv r hr (Pi.single j v)=Pi.single ((orbitChart r hr).symm j) v := by
  apply (coordinateEquiv r hr).symm.injective
  rw [LinearEquiv.symm_apply_apply,coordinateEquiv_symm_single,Equiv.apply_symm_apply]

variable (C : Subgroup (W (R := Blocks) (I := Blocks)))

abbrev actualRepresentation := BinaryPlaneCyclicWreathUniform.representation C

private theorem actual_single (g : C) (i : Blocks) (v : Plane) :
    actualRepresentation C g (Pi.single i v)=
      Pi.single ((g : W (R := Blocks) (I := Blocks)).right*i) ((g : W (R := Blocks) (I := Blocks)).left ((g : W (R := Blocks) (I := Blocks)).right*i) v) := by
  funext j
  change (g : W (R := Blocks) (I := Blocks)).left j ((Pi.single i v : Blocks → Plane) ((g : W (R := Blocks) (I := Blocks)).right⁻¹*j))=_
  by_cases hj : j=(g : W (R := Blocks) (I := Blocks)).right*i
  · subst j
    rw [inv_mul_cancel_left,Pi.single_eq_same,Pi.single_eq_same]
  · have hn : (g : W (R := Blocks) (I := Blocks)).right⁻¹*j≠i := by
      intro h
      apply hj
      calc
        j=(g : W (R := Blocks) (I := Blocks)).right*((g : W (R := Blocks) (I := Blocks)).right⁻¹*j) := by group
        _=(g : W (R := Blocks) (I := Blocks)).right*i := congrArg (fun z => (g : W (R := Blocks) (I := Blocks)).right*z) h
    rw [Pi.single_eq_of_ne hn,Pi.single_eq_of_ne hj,map_zero]

private def transported (r : Blocks) (hr : r≠1) :
    Representation (ZMod 2) C (Index → Plane) :=
  (coordinateEquiv r hr).conjRingEquiv.toMonoidHom.comp (actualRepresentation C)

private theorem transported_apply (r : Blocks) (hr : r≠1)
    (g : C) (v : Index → Plane) : transported C r hr g v=
      coordinateEquiv r hr (actualRepresentation C g ((coordinateEquiv r hr).symm v)) := rfl

private theorem transported_single (r : Blocks) (hr : r≠1)
    (g : C) (i : Index) (v : Plane) :
    transported C r hr g (Pi.single i v)=
      Pi.single ((orbitChart r hr).symm ((g : W (R := Blocks) (I := Blocks)).right*orbitChart r hr i))
        ((g : W (R := Blocks) (I := Blocks)).left ((g : W (R := Blocks) (I := Blocks)).right*orbitChart r hr i) v) := by
  rw [transported_apply,coordinateEquiv_symm_single,actual_single,coordinateEquiv_single]

/-- Every actual rank-one odd kernel with full regular V4 block image
has uniform translation capacity two, without F4 restriction of scalars. -/
theorem uniform (e : oddKernel C ≃* Cubic)
    (honto : Function.Surjective (BinaryPlaneRankOneCommutingInvolution.top C)) :
    UniformSubrepresentationGeneratorBound (actualRepresentation C) 2 := by
  have htrans : ∀ i j : Blocks, ∃ h : C, (h : W (R := Blocks) (I := Blocks)).right • i=j := by
    intro i j
    obtain ⟨h,hh⟩ := honto (j*i⁻¹)
    refine ⟨h,?_⟩
    change (h : W (R := Blocks) (I := Blocks)).right*i=j
    change (h : W (R := Blocks) (I := Blocks)).right=j*i⁻¹ at hh
    rw [hh]
    group
  obtain ⟨s,hs,ht,hcomm⟩ := BinaryPlaneRankOneCommutingInvolution.exists_involution
    C e honto htrans
  let r := BinaryPlaneRankOneCommutingInvolution.top C s
  have hr : r≠1 := ht
  let k := BinaryPlaneRankOneOddGenerator.generator C e
  let rho := transported C r hr
  let K : Index → Plane ≃ₗ[ZMod 2] Plane :=
    fun i => localLinear C (orbitChart r hr i) k
  let L : Index → Plane ≃ₗ[ZMod 2] Plane :=
    fun i => (s : W (R := Blocks) (I := Blocks)).left (r*orbitChart r hr i)
  have hk : (k : C)^3=1 := congrArg (fun z : oddKernel C => (z : C))
    (BinaryPlaneRankOneOddGenerator.generator_cube C e)
  have hc : Commute (k : C) s := (hcomm k).symm
  have hK : ∀ i v, rho (k : C) (Pi.single i v)=Pi.single i (K i v) := by
    intro i v
    rw [transported_single,top_one C k,one_mul,Equiv.symm_apply_apply]
    rfl
  have hL : ∀ i v, rho s (Pi.single i v)=Pi.single (flip i) (L i v) := by
    intro i v
    rw [transported_single]
    have hi : (orbitChart r hr).symm ((s : W (R := Blocks) (I := Blocks)).right*orbitChart r hr i)=flip i := by
      apply (orbitChart r hr).injective
      rw [Equiv.apply_symm_apply,orbitChart_flip]
      rfl
    rw [hi]
    rfl
  have hfixed : ∀ i v, K i v=v → v=0 := by
    intro i v hv
    exact BinaryPlaneRankOneOddGenerator.local_fixedFree C e htrans
      (orbitChart r hr i) v hv
  have hnew := BinaryCubicTwoOrbitPolynomialUniform.uniform rho (k : C) s hk hs hc
    K L hK hL hfixed
  let F : Representation.IntertwiningMap (actualRepresentation C) rho :=
    { toLinearMap := (coordinateEquiv r hr).toLinearMap
      isIntertwining' g := by
        apply LinearMap.ext
        intro v
        change coordinateEquiv r hr (actualRepresentation C g v)=
          coordinateEquiv r hr (actualRepresentation C g
            ((coordinateEquiv r hr).symm (coordinateEquiv r hr v)))
        rw [LinearEquiv.symm_apply_apply] }
  exact hnew.of_injective F (coordinateEquiv r hr).injective

/-- This endpoint keeps any supplied ORIGINAL retained subspace and
quotient map; it introduces no independent quotient or splitting. -/
theorem section_uniform (e : oddKernel C ≃* Cubic)
    (honto : Function.Surjective (BinaryPlaneRankOneCommutingInvolution.top C))
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (S : Subrepresentation (actualRepresentation C)) (sigma : Representation (ZMod 2) C V)
    (q : Representation.IntertwiningMap S.toRepresentation sigma)
    (hq : Function.Surjective q) : UniformSubrepresentationGeneratorBound sigma 2 := by
  let F : Representation.IntertwiningMap S.toRepresentation (actualRepresentation C) :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' _ := rfl }
  exact ((uniform C e honto).of_injective F Subtype.val_injective).of_surjective q hq

end SymmetricSubgroupAsymptotics.BinaryPlaneRankOneKleinUniform
