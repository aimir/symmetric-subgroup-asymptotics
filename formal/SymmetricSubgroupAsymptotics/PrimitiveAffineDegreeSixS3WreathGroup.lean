import SymmetricSubgroupAsymptotics.Non2PreE7C2Wreath
import SymmetricSubgroupAsymptotics.OddMarker

/-!
# The literal degree-six `S₃ ≀ C₂` group and its binary quotient

This lightweight module contains only the finite wreath groups, the
coordinatewise sign quotient, and the faithful four-point action of its
binary quotient.  The asymptotic source package is kept in
`PrimitiveAffineDegreeSixS3WreathSource`; elementary semidirect-coordinate
arguments can therefore import this file without loading that package.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace DegreeSixS3Wreath

private abbrev S3 := Equiv.Perm (Fin 3)
private abbrev C2 := Multiplicative (ZMod 2)

/-- A computational enumeration of a two-block wreath product.  Defining
this from the literal constructor, rather than transporting the product
enumeration through `SemidirectProduct.equivProd`, keeps finite checks free
of non-reducing equality transports. -/
@[reducible] private def wreathFintype (A : Type*) [Group A] [Fintype A] :
    Fintype (C2Wreath.W A) where
  elems := (Finset.univ : Finset ((A × A) × C2)).map
    { toFun := fun p => ⟨p.1, p.2⟩
      inj' := by
        intro p q h
        exact Prod.ext (congrArg SemidirectProduct.left h)
          (congrArg SemidirectProduct.right h) }
  complete x := by
    apply Finset.mem_map.mpr
    exact ⟨(x.left, x.right), Finset.mem_univ _, rfl⟩

/-- The exact full two-block wreath target. -/
abbrev G := C2Wreath.W S3

instance : Fintype G := wreathFintype S3

/-- Its sign quotient, the dihedral group of order eight. -/
abbrev D8 := C2Wreath.W C2

instance : Fintype D8 := wreathFintype C2

def signBase : S3 × S3 →* C2 × C2 :=
  oddMarkerSign.prodMap oddMarkerSign

private theorem signBase_swap_compatible (g : C2) :
    signBase.comp (C2Wreath.swapAut S3 g).toMonoidHom =
      (C2Wreath.swapAut C2 g).toMonoidHom.comp signBase := by
  apply MonoidHom.ext
  intro x
  rcases C2Wreath.cases g with rfl | rfl
  · simp [signBase]
  · simp [signBase, C2Wreath.swapAut_gen]

/-- Coordinatewise sign and the unchanged block swap. -/
def projection : G →* D8 :=
  SemidirectProduct.map signBase (MonoidHom.id C2) signBase_swap_compatible

theorem projection_surjective : Function.Surjective projection := by
  intro y
  obtain ⟨a, ha⟩ := oddMarkerSign_surjective y.left.1
  obtain ⟨b, hb⟩ := oddMarkerSign_surjective y.left.2
  refine ⟨⟨(a, b), y.right⟩, ?_⟩
  apply SemidirectProduct.ext
  · exact Prod.ext ha hb
  · rfl

private abbrev PairPoint := Fin 1 ⊕ Fin 1

/-- The regular two-point action of the base `C₂`. -/
def c2Action : C2 →* Equiv.Perm PairPoint :=
  C2Wreath.blockSwap (Fin 1)

theorem c2Action_injective : Function.Injective c2Action := by
  rw [injective_iff_map_eq_one]
  intro x hx
  rcases C2Wreath.cases x with h | h
  · exact h
  · exfalso
    rw [h, c2Action, C2Wreath.blockSwap] at hx
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, C2Wreath.gen_ne_one,
      if_false] at hx
    have := congrArg (fun sigma : Equiv.Perm PairPoint => sigma (Sum.inl 0)) hx
    simp at this

/-- Flatten the two binary blocks to four points. -/
def d8PointEquiv : PairPoint ⊕ PairPoint ≃ Fin 4 :=
  (Equiv.sumCongr finSumFinEquiv finSumFinEquiv).trans finSumFinEquiv

/-- The faithful imprimitive four-point action of `D₈`. -/
def d8Action : D8 →* Equiv.Perm (Fin 4) :=
  d8PointEquiv.permCongrHom.toMonoidHom.comp
    (C2Wreath.action c2Action)

theorem d8Action_injective : Function.Injective d8Action :=
  d8PointEquiv.permCongrHom.injective.comp
    (C2Wreath.action_injective c2Action c2Action_injective)

theorem card_G : Nat.card G = 72 := by
  rw [SemidirectProduct.card, Nat.card_prod, Nat.card_perm, Nat.card_fin]
  norm_num

theorem card_D8 : Nat.card D8 = 8 := by
  have hc2 : Nat.card C2 = 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  rw [SemidirectProduct.card, Nat.card_prod, hc2]

end DegreeSixS3Wreath
end SymmetricSubgroupAsymptotics

end
