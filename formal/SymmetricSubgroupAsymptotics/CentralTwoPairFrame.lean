import SymmetricSubgroupAsymptotics.TransitiveBinaryPairFrame
import SymmetricSubgroupAsymptotics.NormalSubgroupOrbitIndex
import SymmetricSubgroupAsymptotics.FaithfulTransitiveCentralCard
import SymmetricSubgroupAsymptotics.BinaryPairMaximalSection

/-! The actual orbits of an original central subgroup of order two form
a literal pair frame. This connects an original central involution to the
maximal-section displacement calculation without assuming a selected
pair system or replacing the original transitive action. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics.CentralTwoPairFrame

variable {X : Type} [Finite X] (U : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive U X] (K : Subgroup U) [K.Normal] (x : X)

/-- The actual original translates of the original K-orbit. -/
abbrev Points : Type := MulAction.orbit U (MulAction.orbit K x)

def pointMap (y : X) : Points U K x :=
  normalOrbitClassesEquivBlockOrbit K x (Quotient.mk'' y)

@[simp] theorem pointMap_val (y : X) :
    (pointMap U K x y : Set X)=MulAction.orbit K y := rfl

theorem pointMap_equivariant (u : U) (y : X) :
    pointMap U K x (u • y)=u • pointMap U K x y := by
  apply Subtype.ext
  change MulAction.orbit K (u • y)=u • MulAction.orbit K y
  exact (MulAction.smul_orbit_eq_orbit_smul K y u).symm

theorem pointMap_surjective : Function.Surjective (pointMap U K x) := by
  intro i
  obtain ⟨o,ho⟩ := (normalOrbitClassesEquivBlockOrbit K x).surjective i
  refine ⟨o.out,?_⟩
  unfold pointMap
  rw [Quotient.out_eq',ho]

private theorem orbit_eq_iff_mem (i : Points U K x) (y : X) :
    MulAction.orbit K y=(i:Set X) ↔ y∈(i:Set X) := by
  obtain ⟨u,hu⟩ := i.property
  change u • MulAction.orbit K x=(i:Set X) at hu
  rw [← hu,MulAction.smul_orbit_eq_orbit_smul]
  exact MulAction.orbit_eq_iff

/-- A fibre is literally the same subset of original points as the
corresponding orbit, including its exact multiplicity. -/
def fibreEquiv (i : Points U K x) : {y : X // pointMap U K x y=i} ≃ i.val where
  toFun y := ⟨y.1,(orbit_eq_iff_mem U K x i y.1).mp (congrArg Subtype.val y.2)⟩
  invFun y := ⟨y.1,Subtype.ext ((orbit_eq_iff_mem U K x i y.1).mpr y.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem orbit_card (hc : K≤Subgroup.center U) (hK : Nat.card K=2) (y : X) :
    Nat.card (MulAction.orbit K y)=2 := by
  let f : K → MulAction.orbit K y := fun z => ⟨(z:U) • y,MulAction.mem_orbit y z⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      exact central_evaluation_injective K.subtype Subtype.val_injective
        (fun z => hc z.property) y (congrArg Subtype.val hab)
    · rintro ⟨z,hz⟩
      obtain ⟨g,hg⟩ := hz
      exact ⟨g,Subtype.ext hg⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm.trans hK

theorem fibre_card (hc : K≤Subgroup.center U) (hK : Nat.card K=2)
    (i : Points U K x) : Nat.card {y : X // pointMap U K x y=i}=2 := by
  rw [Nat.card_congr (fibreEquiv U K x i)]
  obtain ⟨y,rfl⟩ := pointMap_surjective U K x i
  exact orbit_card U K hc hK y

/-- The frame is built from the actual central subgroup's two-point
orbits, with the original action on those actual subsets. -/
def frame (hc : K≤Subgroup.center U) (hK : Nat.card K=2) :
    BinaryPairFrame U (Points U K x) :=
  binaryPairFrameOfFibreCardTwo U (MulAction.toPermHom U (Points U K x))
    (pointMap U K x) (pointMap_equivariant U K x) (fibre_card U K x hc hK)

theorem kernel_le (hc : K≤Subgroup.center U) (hK : Nat.card K=2) :
    K≤(frame U K x hc hK).top.ker := by
  intro z hz
  change MulAction.toPermHom U (Points U K x) z=1
  apply Equiv.ext
  intro i
  obtain ⟨y,rfl⟩ := pointMap_surjective U K x i
  change z • pointMap U K x y=pointMap U K x y
  rw [← pointMap_equivariant U K x z y]
  apply Subtype.ext
  change MulAction.orbit K (z • y)=MulAction.orbit K y
  exact MulAction.orbit_eq_iff.mpr ⟨⟨z,hz⟩,rfl⟩

/-- Every nonidentity original central element flips every original pair. -/
theorem bits_one (hc : K≤Subgroup.center U) (hK : Nat.card K=2)
    (z : K) (hz : z≠1) (i : Points U K x) :
    (frame U K x hc hK).bits
      ⟨(z:U),kernel_le U K x hc hK z.property⟩ i=1 := by
  let F := frame U K x hc hK
  let z' : F.top.ker := ⟨(z:U),kernel_le U K x hc hK z.property⟩
  have hfree : ∀ y : X, (z:U) • y≠y := by
    intro y hy
    apply hz
    apply central_evaluation_injective K.subtype Subtype.val_injective
      (fun g => hc g.property) y
    simpa only [map_one,one_smul] using hy
  have hbits : ∀ b : ZMod 2, b=0 ∨ b=1 := by decide +kernel
  rcases hbits (F.bits z' i) with hzero | hone
  · exfalso
    apply hfree (F.frame (i,0))
    have he := F.kernel_action_frame z' i 0
    simpa only [hzero,zero_add] using he
  · exact hone

theorem degree_product (hc : K≤Subgroup.center U) (hK : Nat.card K=2) :
    2*Nat.card (Points U K x)=Nat.card X := by
  have h := Nat.card_congr (frame U K x hc hK).frame
  simpa only [Nat.card_prod,Nat.card_zmod,Nat.mul_comm] using h

theorem points_card_four (hc : K≤Subgroup.center U) (hK : Nat.card K=2)
    (hX : Nat.card X=8) : Nat.card (Points U K x)=4 := by
  have h := degree_product U K x hc hK
  omega

end SymmetricSubgroupAsymptotics.CentralTwoPairFrame
