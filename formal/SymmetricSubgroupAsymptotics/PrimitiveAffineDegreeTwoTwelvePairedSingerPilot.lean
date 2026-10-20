import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveThreeQuartetAlternateCore
import SymmetricSubgroupAsymptotics.FunctionBlockOrbitProjectionIrreducibility

/-! Exact paired-Singer pilot for original row251. Every normal quotient
retains the original literal action and quotient map. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairedSingerPilot

open BinaryPlanePermutationAffineEquiv BinaryPlanePermutationWreathCoordinates
open BinaryPlaneWreathIrreducible
open PrimitiveAffineDegreeTwoTwelveThreeQuartetAlternateCore
open PrimitiveAffineDegreeTwoTwelveThreeQuartetAlternatePilot
open Non2UnipotentPrefixFiniteMenu Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

abbrev Blocks := Equiv.Perm (Fin 3)
abbrev Point := PointWreath (R := Blocks)
abbrev Lin := LinearWreath (R := Blocks)

def pointLifts : Fin 5 → Point :=
  ![
  ⟨![localPerm 1,localPerm 1,localPerm (Equiv.swap 0 3 * Equiv.swap 1 2)],1⟩,
  ⟨![localPerm 1,localPerm 1,localPerm (Equiv.swap 0 2 * Equiv.swap 1 3)],1⟩,
  ⟨![localPerm (Equiv.swap 1 2 * Equiv.swap 1 3),localPerm 1,localPerm (Equiv.swap 0 3 * Equiv.swap 0 1)],1⟩,
  ⟨![localPerm (Equiv.swap 0 2 * Equiv.swap 1 3),localPerm (Equiv.swap 0 3 * Equiv.swap 0 2 * Equiv.swap 0 1),localPerm (Equiv.swap 0 3 * Equiv.swap 0 2 * Equiv.swap 0 1)],(Equiv.swap 0 2 * Equiv.swap 0 1)⟩,
  ⟨![localPerm (Equiv.swap 0 1 * Equiv.swap 0 2),localPerm (Equiv.swap 0 2 * Equiv.swap 0 1),localPerm (Equiv.swap 1 2)],(Equiv.swap 0 1)⟩]
def lifted : Fin 5 → BinaryThreeQuartetLiteralSocles.Model (R := Blocks) :=
  fun i => coordinates (pointLifts i)

theorem bindings (i : Fin 5) :
    BinaryThreeQuartetLiteralSocles.action (lifted i) = row251Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

def z : Lin := (lifted 2).right
def g : Lin := (lifted 3).right
def pairWord : Fin 3 → Lin := ![z,g*z*g⁻¹,g^2*z*(g^2)⁻¹]
def projectionIndex : Fin 3 → Fin 3 := ![2,0,1]

theorem pair_projection (i : Fin 3) (v : Fin 3 → V) :
    v * action (pairWord (projectionIndex i)) v *
      action ((pairWord (projectionIndex i))^2) v = Pi.mulSingle i (v i) := by
  funext j
  revert i v j
  decide +kernel

theorem pair_local_orbit (i : Fin 3) (u v : V) (hu : u ≠ 1) (hv : v ≠ 1) :
    ∃ n : Fin 3, action ((pairWord i)^n.val) (Pi.mulSingle i u) = Pi.mulSingle i v := by
  have h : ∃ n : Fin 3, ∀ (j : Fin 3) (t : Fin 2),
      ((action ((pairWord i)^n.val) (Pi.mulSingle i u)) j).toAdd t =
        ((Pi.mulSingle i v : Fin 3 → V) j).toAdd t := by
    revert i u v hu hv
    decide +kernel
  obtain ⟨n,hn⟩ := h
  refine ⟨n,?_⟩
  funext j
  apply Multiplicative.toAdd.injective
  exact funext (hn j)

theorem pair_mem (C : Subgroup Lin) (hz : z ∈ C) (hg : g ∈ C) (i : Fin 3) :
    pairWord i ∈ C := by
  fin_cases i
  · exact hz
  · exact C.mul_mem (C.mul_mem hg hz) (C.inv_mem hg)
  · exact C.mul_mem (C.mul_mem (C.pow_mem hg 2) hz) (C.inv_mem (C.pow_mem hg 2))

theorem quotientSocle (N : Subgroup Row251Top) [N.Normal] :
    SocleNormalGeneratorBound (Row251Top ⧸ N) 3 := by
  let K := Subgroup.closure (Set.range lifted)
  let C := BinaryPlaneWreathNormalGenerators.actualImage K
  have hgen (j : Fin 5) : (lifted j).right ∈ C :=
    ⟨closureGenerators lifted j,rfl⟩
  have hz : z ∈ C := hgen 2
  have hg : g ∈ C := hgen 3
  have hw (j : Fin 3) : pairWord j ∈ C := pair_mem C hz hg j
  let beta : C →* Blocks := PermutationalWreathProduct.rightHom.comp C.subtype
  have hfull : Subgroup.closure (Set.range (fun i => (lifted i).right.right)) = ⊤ :=
    symmetric_full (fun i => (lifted i).right.right) 3 4
      (by apply Equiv.ext; intro j; revert j; decide +kernel)
      (by apply Equiv.ext; intro j; revert j; decide +kernel)
  have hbeta : Function.Surjective beta := by
    have htop : (⊤ : Subgroup Blocks) ≤ beta.range := by
      rw [← hfull]
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨j,rfl⟩
      exact ⟨⟨(lifted j).right,hgen j⟩,rfl⟩
    intro r
    exact htop (Subgroup.mem_top r)
  have hmove : ∀ i j : Fin 3, ∃ q : C, (q : Lin).right • i = j := by
    intro i j
    obtain ⟨r,hr⟩ := symmetric_transitive i j
    obtain ⟨q,hq⟩ := hbeta r
    exact ⟨q,by change beta q • i = j; rw [hq,hr]⟩
  have hirr : IrreducibleAbelianSemidirect.Irreducible (restrictedAction C) := by
    apply functionBlock_irreducible_of_three_term_projection_and_local_orbits
      (restrictedAction C) ?_ ?_
      (fun i => ⟨pairWord (projectionIndex i),hw (projectionIndex i)⟩) ?_
    · intro i u v hu hv
      obtain ⟨n,hn⟩ := pair_local_orbit i u v hu hv
      exact ⟨⟨(pairWord i)^n.val,C.pow_mem (hw i) n.val⟩,hn⟩
    · intro i j
      obtain ⟨q,hq⟩ := hmove i j
      refine ⟨q,localAction ((q : Lin).left j),?_⟩
      intro v
      change action (q : Lin) (Pi.mulSingle i v) = _
      rw [action_single,hq]
    · intro i v
      exact pair_projection i v
  have htuples := IrreducibleAbelianSemidirectSubgroup.normal_generating_tuples
    BinaryPlaneWreathIrreducible.action K
    (BinaryPlaneWreathIrreducible.action_injective.comp Subtype.val_injective)
    hirr (by omega : 0 < 3)
    (BinaryPlaneWreathNormalGenerators.normal_generating_tuples C hbeta
      symmetricRotation 0 symmetric_cycle 1 symmetric_normalGen)
  let f : K →* Equiv.Perm (Fin 12) := BinaryThreeQuartetLiteralSocles.action.comp K.subtype
  let pi := GeneratedLiteralImage.toTop f (closureGenerators lifted) row251Generators
    (Equiv.refl _) (closureGenerators_full lifted) bindings
  have hpi : Function.Surjective pi :=
    GeneratedLiteralImage.toTop_surjective f (closureGenerators lifted) row251Generators
      (Equiv.refl _) (closureGenerators_full lifted) bindings
  exact normal_generating_tuples_of_surjective ((QuotientGroup.mk' N).comp pi)
    ((QuotientGroup.mk'_surjective N).comp hpi) htuples
    (finiteGroupSocle _) inferInstance

def family : row251Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row251Interface.normalRegistry (fun N => by letI := N.2; exact quotientSocle N.1)

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairedSingerPilot

end
