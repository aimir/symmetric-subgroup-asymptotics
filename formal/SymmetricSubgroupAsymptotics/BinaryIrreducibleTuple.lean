import SymmetricSubgroupAsymptotics.CentralCharacterConstituent
import SymmetricSubgroupAsymptotics.BinaryCentralOmegaDetection
import Mathlib.Tactic.FinCases

/-! A finite binary group has a jointly faithful tuple of irreducible
representations indexed by a basis of its actual central involutions.
The tuple is constructed from central scalar characters; its faithfulness
uses the intersection theorem for actual normal subgroups. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra
namespace SymmetricSubgroupAsymptotics

structure FiniteIrreducibleRepresentation (k G : Type) [Field k] [Group G] where
  Space : Type
  addCommGroup : AddCommGroup Space
  module : Module k Space
  finiteDimensional : FiniteDimensional k Space
  action : Representation k G Space
  irreducible : Representation.IsIrreducible action

attribute [instance] FiniteIrreducibleRepresentation.addCommGroup
  FiniteIrreducibleRepresentation.module FiniteIrreducibleRepresentation.finiteDimensional
  FiniteIrreducibleRepresentation.irreducible

variable {k G : Type} [Field k] [Group G]

theorem exists_bundled_central_character [Finite G] [NeZero (Nat.card G:k)]
    (H : Subgroup G) (hH : H≤Subgroup.center G) (χ : H→*k) :
    ∃ ρ : FiniteIrreducibleRepresentation k G,
      ∀ (h : H) (v : ρ.Space),ρ.action (h:G) v=χ h • v := by
  obtain ⟨W,hW,hM,hF,ρ,hi,hs⟩ := exists_irreducible_central_character H hH χ
  exact ⟨⟨W,hW,hM,hF,ρ,hi⟩,hs⟩

def binaryScalarSign : Multiplicative (ZMod 2)→*k where
  toFun x := if x.toAdd=0 then 1 else -1
  map_one' := by simp
  map_mul' x y := by
    change (if x.toAdd+y.toAdd=0 then 1 else -1)=
      (if x.toAdd=0 then 1 else -1)*(if y.toAdd=0 then 1 else -1)
    have hx : x.toAdd=0 ∨ x.toAdd=1 := by
      generalize x.toAdd=z
      fin_cases z <;> simp
    have hy : y.toAdd=0 ∨ y.toAdd=1 := by
      generalize y.toAdd=z
      fin_cases z <;> simp
    rcases hx with hx|hx <;> rcases hy with hy|hy <;> simp [hx,hy]

theorem binaryScalarSign_eq_one [CharZero k] (x : Multiplicative (ZMod 2)) :
    binaryScalarSign (k := k) x=1 ↔ x=1 := by
  change (if x.toAdd=0 then (1:k) else -1)=1 ↔ x=1
  by_cases h:x.toAdd=0
  · have hx : x=1 := Multiplicative.toAdd.injective h
    simp [hx]
  · have hx : x≠1 := fun he=>h (congrArg Multiplicative.toAdd he)
    simp [h,hx,neg_eq_iff_add_eq_zero]

def binaryOmegaSubgroup (G : Type) [Group G] : Subgroup G :=
  (binaryCentralOmegaEmbedding (G := G)).range

def binaryOmegaSubgroupEquiv : binaryCentralOmega G≃*binaryOmegaSubgroup G :=
  MonoidHom.ofInjective binaryCentralOmegaEmbedding_injective

theorem binaryOmegaSubgroup_central : binaryOmegaSubgroup G≤Subgroup.center G := by
  rintro g ⟨z,rfl⟩
  exact z.val.property

def binaryOmegaCoordinate [Finite G]
    (i : Fin (Module.finrank (ZMod 2) (Additive (binaryCentralOmega G)))) :
    binaryCentralOmega G→*Multiplicative (ZMod 2) where
  toFun z := Multiplicative.ofAdd
    ((Module.finBasis (ZMod 2) (Additive (binaryCentralOmega G))).repr (Additive.ofMul z) i)
  map_one' := by simp
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    exact congrFun (congrArg DFunLike.coe
      ((Module.finBasis (ZMod 2) (Additive (binaryCentralOmega G))).repr.map_add
        (Additive.ofMul x) (Additive.ofMul y))) i

theorem binaryOmegaCoordinate_faithful [Finite G] (z : binaryCentralOmega G)
    (hz : ∀ i,binaryOmegaCoordinate i z=1) : z=1 := by
  apply Additive.ofMul.injective
  change Additive.ofMul z=0
  apply (Module.finBasis (ZMod 2) (Additive (binaryCentralOmega G))).repr.injective
  apply Finsupp.ext
  intro i
  simpa only [map_zero,Finsupp.zero_apply] using congrArg Multiplicative.toAdd (hz i)

def binaryOmegaScalarCharacter [Finite G]
    (i : Fin (Module.finrank (ZMod 2) (Additive (binaryCentralOmega G)))) :
    binaryOmegaSubgroup G→*k :=
  binaryScalarSign.comp ((binaryOmegaCoordinate i).comp binaryOmegaSubgroupEquiv.symm.toMonoidHom)

theorem exists_binary_faithful_irreducible_tuple [Finite G] [CharZero k]
    (hG : IsPGroup 2 G) :
    ∃ ρ : Fin (Module.finrank (ZMod 2) (Additive (binaryCentralOmega G)))→
        FiniteIrreducibleRepresentation k G,
      ∀ g : G, (∀ i, (ρ i).action g = 1) → g = 1 := by
  classical
  letI : NeZero (Nat.card G:k) := ⟨by exact_mod_cast (Nat.card_pos (α := G)).ne'⟩
  have he (i : Fin (Module.finrank (ZMod 2) (Additive (binaryCentralOmega G)))) :=
    exists_bundled_central_character (binaryOmegaSubgroup G) binaryOmegaSubgroup_central
      (binaryOmegaScalarCharacter (k := k) i)
  choose ρ hρ using he
  refine ⟨ρ,binaryCentralOmega_joint_kernel_detection hG (fun i=>(ρ i).action) ?_⟩
  intro z hz
  apply binaryOmegaCoordinate_faithful
  intro i
  apply (binaryScalarSign_eq_one (k := k) _).mp
  let h : binaryOmegaSubgroup G := binaryOmegaSubgroupEquiv z
  have hs (v : (ρ i).Space) := hρ i h v
  have hval : (h:G)=binaryCentralOmegaEmbedding z := rfl
  simp only [hval,hz i,Module.End.one_apply] at hs
  letI : Nontrivial (ρ i).action.asModule :=
    IsSimpleModule.nontrivial k[G] (ρ i).action.asModule
  letI : Nontrivial (ρ i).Space := (ρ i).action.asModuleEquiv.toEquiv.symm.nontrivial
  obtain ⟨v,hv⟩ := exists_ne (0:(ρ i).Space)
  have hscalar : binaryOmegaScalarCharacter (k := k) i h=1 :=
    (smul_left_injective k hv) (by simpa using (hs v).symm)
  simpa only [binaryOmegaScalarCharacter,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
    h,MulEquiv.symm_apply_apply] using hscalar

end SymmetricSubgroupAsymptotics
