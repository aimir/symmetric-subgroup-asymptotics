import SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleRootNoncommutation
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckOriginalRankOneWitness
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrthogonalWeyl
import Mathlib.GroupTheory.Subgroup.Centralizer

/-! The unique positive commutation edge between paired and singleton
simple labels is detected in the ORIGINAL model. The noncommuting
middle witness survives by the proved positive restriction injection;
all other cross-shape groups commute by orthogonal root relations. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckCrossShapeRootCommutation
open CFSGE6GeckMiddleRootNoncommutation CFSGE6GeckOrbitRootIntersection
open CFSGTwistedE6GeckOriginalRankOneWitness CFSGTwistedE6GeckOriginalRootIntersection
open CFSGTwistedE6GeckOriginalOppositeAlignment CFSGTwistedE6GeckOriginalProjection
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckRootGeneratedPGroup
open CFSGTwistedE6GeckDiagramCovariance CFSGE6GeckRelativeSimpleHom
open CFSGTwistedE6RelativeWeylOrbits CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGNormTwoGeckOrthogonalWeyl
open CFSGSerreOrdinaryTwists CFSGSerreQuadraticMatrix
local notation "A" => CartanMatrix.E₆

private theorem cross_cartan_zero (a b : Fin 4) (ha : a.val<2) (hb : 2≤b.val)
    (hedge : a≠1 ∨ b≠2) (i : Fin 6) (hi : i∈orbitWord a) (j : Fin 6) (hj : j∈orbitWord b) :
    CFSGGeckSerreRepresentation.cartan E6Base E6Index i j=0 := by
  rw [E6_cartan]
  have h : ∀a b : Fin 4,a.val<2→2≤b.val→(a≠1 ∨ b≠2)→
    ∀i∈orbitWord a,∀j∈orbitWord b,A i j=0 := by decide
  exact h a b ha hb hedge i hi j hj

theorem cross_shape_raw_commute (K : Type) [Field K] (a b : Fin 4)
    (ha : a.val<2) (hb : 2≤b.val) (hedge : a≠1 ∨ b≠2)
    (x : (Matrix GeckIndex GeckIndex K)ˣ) (hx : x∈orbitPositiveGroup K a)
    (y : (Matrix GeckIndex GeckIndex K)ˣ) (hy : y∈orbitPositiveGroup K b) : Commute x y := by
  have hc : orbitPositiveGroup K a≤Subgroup.centralizer
      (orbitPositiveGroup K b : Set ((Matrix GeckIndex GeckIndex K)ˣ)) := by
    apply iSup_le
    intro i
    apply iSup_le
    intro hi
    apply Subgroup.le_centralizer_iff.mpr
    apply iSup_le
    intro j
    apply iSup_le
    intro hj
    rintro z ⟨t,rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro u ⟨s,rfl⟩
    exact (orthogonal_signed_roots A CartanMatrix.E₆_transpose E6_positive_definite E6Base E6Index K
      i j (cross_cartan_zero a b ha hb hedge i hi j hj) false false s t).eq
  exact (Subgroup.mem_centralizer_iff.mp (hc hx) y hy).symm

theorem original_cross_shape_commute (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] (a b : Fin 4)
    (ha : a.val<2) (hb : 2≤b.val) (hedge : a≠1 ∨ b≠2)
    (x : CFSG.Models.TwistedE6 q) (hx : x∈originalOrbitRoot q a)
    (y : CFSG.Models.TwistedE6 q) (hy : y∈originalOrbitRoot q b) : Commute x y := by
  obtain ⟨u,hu,rfl⟩ := hx
  obtain ⟨v,hv,rfl⟩ := hy
  let ju := signedFixedToGenerated q false u
  let jv := signedFixedToGenerated q false v
  have hc := cross_shape_raw_commute (q.Extension 2) a b ha hb hedge u.val hu v.val hv
  have hJ : Commute ju jv := Subtype.ext hc.eq
  change Commute (generatedToOriginal q ju) (generatedToOriginal q jv)
  exact hJ.map (generatedToOriginal q)

private theorem reflect_commute {G Q : Type*} [Group G] [Group Q]
    (f : G→*Q) (U : Subgroup G) (hf : Function.Injective (f.comp U.subtype))
    (u v : U) (hc : Commute (f u.val) (f v.val)) : Commute u.val v.val := by
  have hm : (f.comp U.subtype) (u*v)=(f.comp U.subtype) (v*u) := by
    simpa only [MonoidHom.comp_apply,Subgroup.coe_mul,map_mul] using hc.eq
  exact congrArg Subtype.val (hf hm)

theorem original_middle_not_commute (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedE6 q)] :
    ¬Commute (originalOrbitOne q false 1) (originalOrbitOne q false 2) := by
  intro hc
  have hm (a : Fin 4) : orbitOneInGenerated q false a∈
      rootPart (q.Extension 2) (definingFieldAutomorphism q 2) false := by
    change rawOrbitHom (q.Extension 2) (definingFieldAutomorphism q 2) false a
      (Multiplicative.ofAdd 1)∈signedFixed (q.Extension 2) (definingFieldAutomorphism q 2) false
    rw [rawOrbitHom_one_parameter]
    exact ⟨orbitParameter_mem_upper (q.Extension 2) false a 1,
      orbitParameter_fixed (q.Extension 2) (definingFieldAutomorphism q 2) false a 1 (map_one _)⟩
  let u : rootPart (q.Extension 2) (definingFieldAutomorphism q 2) false :=
    ⟨orbitOneInGenerated q false 1,hm 1⟩
  let v : rootPart (q.Extension 2) (definingFieldAutomorphism q 2) false :=
    ⟨orbitOneInGenerated q false 2,hm 2⟩
  have hJ := reflect_commute (generatedToOriginal q) _ (rootPart_positive_original_injective q) u v hc
  have hraw : Commute u.val.val v.val.val :=
    congrArg (fun z : fixedRootGenerated (q.Extension 2) (definingFieldAutomorphism q 2)=>z.val) hJ.eq
  change Commute (rawOrbitHom (q.Extension 2) (definingFieldAutomorphism q 2) false 1
    (Multiplicative.ofAdd 1)) (rawOrbitHom (q.Extension 2) (definingFieldAutomorphism q 2) false 2
      (Multiplicative.ofAdd 1)) at hraw
  rw [rawOrbitHom_one_parameter,rawOrbitHom_one_parameter] at hraw
  exact middle_parameter_not_commute (q.Extension 2) hraw

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckCrossShapeRootCommutation
