import SymmetricSubgroupAsymptotics.PGroupPrimeIndexChain
import SymmetricSubgroupAsymptotics.PrimitiveBlockFibre
import SymmetricSubgroupAsymptotics.BinaryPairFrameEquivariance

/-! A transitive finite 2-group has a pair frame on its original points.
The pairs are the actual fibres belonging to a cover of the original point
stabilizer. The top group is the literal quotient-action range. The existing
faithful kernel chart retains every correlation among the original flips;
no full wreath-product base is substituted for that kernel. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

private def pairFibreBitEquiv {X I : Type*} [Finite X]
    (b : X → I) (hcard : ∀ i, Nat.card {x : X // b x=i}=2) (i : I) :
    ZMod 2 ≃ {x : X // b x=i} := by
  letI := Fintype.ofFinite {x : X // b x=i}
  exact Fintype.equivOfCardEq (by
    simp only [← Nat.card_eq_fintype_card, Nat.card_zmod, hcard])

private def pairFibreFrame {X I : Type*} [Finite X]
    (b : X → I) (hcard : ∀ i, Nat.card {x : X // b x=i}=2) : I × ZMod 2 ≃ X :=
  (Equiv.sigmaEquivProd I (ZMod 2)).symm.trans
    ((Equiv.sigmaCongrRight (pairFibreBitEquiv b hcard)).trans (Equiv.sigmaFiberEquiv b))

private theorem pairFibreFrame_map {X I : Type*} [Finite X]
    (b : X → I) (hcard : ∀ i, Nat.card {x : X // b x=i}=2) (p : I × ZMod 2) :
    b (pairFibreFrame b hcard p)=p.1 :=
  (pairFibreBitEquiv b hcard p.1 p.2).property

/-- An actual equivariant map whose complete fibres have two points gives
a frame with exactly the supplied original top action. -/
def binaryPairFrameOfFibreCardTwo {X I : Type*} [Finite X]
    (U : Subgroup (Equiv.Perm X)) (top : U →* Equiv.Perm I) (b : X → I)
    (hb : ∀ (u : U) x, b ((u : Equiv.Perm X) x)=top u (b x))
    (hcard : ∀ i, Nat.card {x : X // b x=i}=2) : BinaryPairFrame U I where
  frame := pairFibreFrame b hcard
  top := top
  intertwine u p := by
    have hinv (x : X) : ((pairFibreFrame b hcard).symm x).1 = b x := by
      have h := pairFibreFrame_map b hcard ((pairFibreFrame b hcard).symm x)
      simpa only [Equiv.apply_symm_apply] using h.symm
    exact (hinv ((u : Equiv.Perm X) (pairFibreFrame b hcard p))).trans
      ((hb u (pairFibreFrame b hcard p)).trans
        (congrArg (fun i : I => top u i) (pairFibreFrame_map b hcard p)))

@[simp] theorem binaryPairFrameOfFibreCardTwo_map {X I : Type*} [Finite X]
    (U : Subgroup (Equiv.Perm X)) (top : U →* Equiv.Perm I) (b : X → I)
    (hb : ∀ (u : U) x, b ((u : Equiv.Perm X) x)=top u (b x))
    (hcard : ∀ i, Nat.card {x : X // b x=i}=2) (p : I × ZMod 2) :
    b ((binaryPairFrameOfFibreCardTwo U top b hb hcard).frame p)=p.1 :=
  pairFibreFrame_map b hcard p

/-- The overgroup and cover are in the original subgroup lattice. The
upper group is allowed to be top, which includes degree two. -/
structure TransitiveBinaryPairCover {X : Type} (U : Subgroup (Equiv.Perm X)) (x : X) where
  subgroup : Subgroup U
  covers : MulAction.stabilizer U x ⋖ subgroup
  relIndex_two : (MulAction.stabilizer U x).relIndex subgroup=2

/-- The prime-index step is derived from the original finite 2-group;
no supplied block system or numerical rank premise is needed. -/
theorem transitiveBinaryPairCover_nonempty {X : Type} [Finite X] [Nontrivial X]
    (U : Subgroup (Equiv.Perm X)) [MulAction.IsPretransitive U X]
    (hU : IsPGroup 2 U) (x : X) : Nonempty (TransitiveBinaryPairCover U x) := by
  classical
  letI : Finite (Subgroup U) :=
    Finite.of_injective (fun H : Subgroup U => (H : Set U)) SetLike.coe_injective
  letI : Fintype (Subgroup U) := Fintype.ofFinite _
  letI : LocallyFiniteOrder (Subgroup U) := Fintype.toLocallyFiniteOrder
  have hne : MulAction.stabilizer U x ≠ ⊤ := by
    intro he
    obtain ⟨y, hy⟩ := exists_ne x
    obtain ⟨u, hu⟩ := MulAction.exists_smul_eq U x y
    have hx : u • x=x := by
      have hmem : u ∈ MulAction.stabilizer U x := by rw [he]; exact Subgroup.mem_top u
      exact hmem
    exact hy (hu.symm.trans hx)
  obtain ⟨H, hcover, _⟩ := exists_covBy_le_of_lt (lt_top_iff_ne_top.mpr hne)
  exact ⟨⟨H, hcover, pGroup_subgroupCover_relIndex hU _ _ hcover⟩⟩

namespace TransitiveBinaryPairCover
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X] {x : X} (D : TransitiveBinaryPairCover U x)

abbrev Points : Type := U ⧸ D.subgroup
abbrev base : D.Points := ((1 : U) : U ⧸ D.subgroup)

def map : X → D.Points := originalTransitiveBlockMap x D.subgroup

theorem map_equivariant (u : U) (y : X) : D.map (u • y)=u • D.map y :=
  originalTransitiveBlockMap_equivariant x D.subgroup D.covers.le u y

theorem map_surjective : Function.Surjective D.map :=
  originalTransitiveBlockMap_surjective x D.subgroup D.covers.le

theorem map_base : D.map x=D.base :=
  originalTransitiveBlockMap_base x D.subgroup D.covers.le

abbrev Fibre (i : D.Points) : Type := {y : X // D.map y=i}

theorem base_fibre_card : Nat.card (D.Fibre D.base)=2 :=
  (originalTransitiveBlockFibre_card x D.subgroup D.covers.le).trans D.relIndex_two

/-- Transport within the original action identifies the actual fibres. -/
def fibreEquiv (i : D.Points) : D.Fibre D.base ≃ D.Fibre i := by
  let u : U := Classical.choose (MulAction.exists_smul_eq U D.base i)
  have hu : u • D.base=i := Classical.choose_spec (MulAction.exists_smul_eq U D.base i)
  exact {
    toFun y := ⟨u • y.1, by rw [D.map_equivariant, y.2, hu]⟩
    invFun y := ⟨u⁻¹ • y.1, by rw [D.map_equivariant, y.2, ← hu, inv_smul_smul]⟩
    left_inv y := Subtype.ext (inv_smul_smul u y.1)
    right_inv y := Subtype.ext (smul_inv_smul u y.1) }

theorem fibre_card (i : D.Points) : Nat.card (D.Fibre i)=2 :=
  (Nat.card_congr (D.fibreEquiv i)).symm.trans D.base_fibre_card

/-- The top map is literally the original action on the original cosets. -/
def frame : BinaryPairFrame U D.Points :=
  binaryPairFrameOfFibreCardTwo U (MulAction.toPermHom U D.Points) D.map
    D.map_equivariant D.fibre_card

@[simp] theorem frame_top : D.frame.top=MulAction.toPermHom U D.Points := rfl

@[simp] theorem frame_map (p : D.Points × ZMod 2) : D.map (D.frame.frame p)=p.1 :=
  binaryPairFrameOfFibreCardTwo_map _ _ _ _ _ p

/-- Its top is a literal permutation subgroup for degree induction. -/
abbrev Top : Subgroup (Equiv.Perm D.Points) := D.frame.top.range

theorem top_pretransitive : MulAction.IsPretransitive D.Top D.Points := by
  constructor
  intro i j
  obtain ⟨u, hu⟩ := MulAction.exists_smul_eq U i j
  exact ⟨D.frame.top.rangeRestrict u, hu⟩

theorem top_faithful : FaithfulSMul D.Top D.Points := inferInstance

theorem top_isPGroup (hU : IsPGroup 2 U) : IsPGroup 2 D.Top :=
  hU.of_surjective D.frame.top.rangeRestrict D.frame.top.rangeRestrict_surjective

theorem top_finite : Finite D.Top :=
  Finite.of_surjective D.frame.top.rangeRestrict D.frame.top.rangeRestrict_surjective

/-- The original point-stabilizer cover acts primitively on its actual
pair fibre; the component is its faithful permutation image. -/
abbrev Component : Subgroup (Equiv.Perm (D.Fibre D.base)) :=
  originalBlockComponent D.map D.map_equivariant D.base

theorem component_preprimitive : MulAction.IsPreprimitive D.Component (D.Fibre D.base) := by
  apply originalBlockComponent_preprimitive D.map D.map_equivariant D.base x D.map_base
  change MulAction.stabilizer U x ⋖ MulAction.stabilizer U ((1 : U) : U ⧸ D.subgroup)
  rw [MulAction.stabilizer_quotient]
  exact D.covers

theorem component_faithful : FaithfulSMul D.Component (D.Fibre D.base) := inferInstance

/-- The physical degree is twice the number of original blocks. -/
theorem degree_product : 2*Nat.card D.Points=Nat.card X := by
  have h := originalTransitiveBlock_degree_product x D.subgroup D.covers.le
  change Nat.card (D.Fibre D.base)*Nat.card D.Points=Nat.card X at h
  rw [D.base_fibre_card] at h
  exact h

theorem points_card_pos : 0<Nat.card D.Points := Nat.card_pos

theorem points_card_lt : Nat.card D.Points<Nat.card X := by
  have hp := D.degree_product
  have hpos := D.points_card_pos
  omega

end TransitiveBinaryPairCover
end SymmetricSubgroupAsymptotics
