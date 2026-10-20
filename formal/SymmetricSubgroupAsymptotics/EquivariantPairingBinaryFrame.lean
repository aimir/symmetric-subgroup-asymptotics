import SymmetricSubgroupAsymptotics.TransitivePairingCount
import SymmetricSubgroupAsymptotics.TransitiveBinaryPairFrame
import SymmetricSubgroupAsymptotics.BinaryPairFrameTransport
import Mathlib.Data.Set.Card

/-! A genuine equivariant partner function gives a binary pair frame on
the SAME original points. The pair index is the actual two-element subset,
so orientations and labels are auxiliary and do not change the action. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise
namespace SymmetricSubgroupAsymptotics.EquivariantPairingBinaryFrame
variable {X : Type} (U : Subgroup (Equiv.Perm X)) (P : EquivariantPairing U X)

def pairSet (x : X) : Set X := {x,P.val x}
abbrev Pairs := Set.range (pairSet U P)

def pointMap (x : X) : Pairs U P := ⟨pairSet U P x,⟨x,rfl⟩⟩

theorem pointMap_surjective : Function.Surjective (pointMap U P) := by
  rintro ⟨s,x,rfl⟩
  exact ⟨x,rfl⟩

instance [Finite X] : Finite (Pairs U P) :=
  Finite.of_surjective (pointMap U P) (pointMap_surjective U P)

private theorem pair_smul (u : U) (x : X) :
    u • pairSet U P x=pairSet U P (u • x) := by
  change (fun z : X => u • z) '' {x,P.val x}={u • x,P.val (u • x)}
  rw [Set.image_pair,P.property.2.2 u x]

instance : MulAction U (Pairs U P) where
  smul u s := ⟨u • s.val,by
    obtain ⟨x,hx⟩ := s.property
    exact ⟨u • x,by rw [← pair_smul U P u x,hx]⟩⟩
  one_smul s := by
    apply Subtype.ext
    exact one_smul U s.val
  mul_smul u v s := by
    apply Subtype.ext
    exact mul_smul u v s.val

theorem pointMap_equivariant (u : U) (x : X) :
    pointMap U P (u • x)=u • pointMap U P x := by
  apply Subtype.ext
  exact (pair_smul U P u x).symm

private theorem pair_eq_iff (x y : X) :
    pairSet U P x=pairSet U P y ↔ x=y ∨ x=P.val y := by
  constructor
  · intro h
    have hx : x∈pairSet U P x := Set.mem_insert _ _
    rw [h] at hx
    exact hx
  · rintro (rfl | rfl)
    · rfl
    · change {P.val y,P.val (P.val y)}=({y,P.val y} : Set X)
      rw [P.property.1 y]
      exact Set.pair_comm _ _

private theorem fibre_mem_iff (s : Pairs U P) (x : X) :
    pointMap U P x=s ↔ x∈s.val := by
  obtain ⟨y,hy⟩ := s.property
  have hs : s=pointMap U P y := Subtype.ext hy.symm
  subst s
  rw [Subtype.ext_iff]
  change pairSet U P x=pairSet U P y ↔ x∈pairSet U P y
  exact pair_eq_iff U P x y

private def fibreEquiv (s : Pairs U P) :
    {x : X // pointMap U P x=s} ≃ s.val where
  toFun x := ⟨x.val,(fibre_mem_iff U P s x.val).mp x.property⟩
  invFun x := ⟨x.val,(fibre_mem_iff U P s x.val).mpr x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem fibre_card (s : Pairs U P) : Nat.card {x : X // pointMap U P x=s}=2 := by
  rw [Nat.card_congr (fibreEquiv U P s)]
  obtain ⟨x,hx⟩ := s.property
  change Nat.card s.val=2
  rw [← hx,Nat.card_coe_set_eq]
  exact Set.ncard_pair (Ne.symm (P.property.2.1 x))

/-- The actual pair subsets carry the literal action induced by U. -/
def frame [Finite X] : BinaryPairFrame U (Pairs U P) :=
  binaryPairFrameOfFibreCardTwo U (MulAction.toPermHom U (Pairs U P))
    (pointMap U P) (pointMap_equivariant U P) (fibre_card U P)

theorem pairs_card [Finite X] (n : ℕ) (hX : Nat.card X=2*n) :
    Nat.card (Pairs U P)=n := by
  have he := Nat.card_congr (frame U P).frame
  rw [Nat.card_prod,Nat.card_zmod,hX] at he
  omega

/-- Reindexing changes labels only; the frame remains on original X. -/
def frameFin [Finite X] (n : ℕ) (hX : Nat.card X=2*n) : BinaryPairFrame U (Fin n) := by
  letI : Fintype (Pairs U P) := Fintype.ofFinite _
  let e : Pairs U P ≃ Fin n := Fintype.equivOfCardEq (by
    rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,Nat.card_fin]
    exact pairs_card U P n hX)
  exact (frame U P).reindex e

end SymmetricSubgroupAsymptotics.EquivariantPairingBinaryFrame
