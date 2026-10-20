import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTransitiveMatch
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFourPairsClassification
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0TopCertificate
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow8TopCertificate
import Mathlib.GroupTheory.Perm.Sign

/-! Actual diagonal A4/S4 on two quartets, with independent quartet swap.
The two original generator lists lie in the faithful product action; their
already proved24/48source cardinalities give equality of the actual ranges.
No abstract-order recognition or new normal census is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FourPairCentralProductCanonicalRows
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
abbrev C2 := Multiplicative (ZMod 2)

private def bitEquiv : C2 ≃ Fin 2 where
  toFun b := (ZMod.finEquiv 2).symm b.toAdd
  invFun i := Multiplicative.ofAdd (ZMod.finEquiv 2 i)
  left_inv b := congrArg Multiplicative.ofAdd ((ZMod.finEquiv 2).apply_symm_apply b.toAdd)
  right_inv i := (ZMod.finEquiv 2).symm_apply_apply i

private def points : Fin 4 × C2 ≃ Fin 8 :=
  (Equiv.prodComm (Fin 4) C2).trans
    ((Equiv.prodCongr bitEquiv (Equiv.refl (Fin 4))).trans finProdFinEquiv)

private def productAction {A : Type} [Group A] (rho : A →* Equiv.Perm (Fin 4)) :
    A × C2 →* Equiv.Perm (Fin 4 × C2) where
  toFun g := Equiv.prodCongr (rho g.1) (Equiv.mulLeft g.2)
  map_one' := by
    apply Equiv.ext
    intro x
    apply Prod.ext
    · exact congrFun (congrArg Equiv.toFun rho.map_one) x.1
    · exact one_mul x.2
  map_mul' g h := by
    apply Equiv.ext
    intro x
    apply Prod.ext
    · exact congrFun (congrArg Equiv.toFun (rho.map_mul g.1 h.1)) x.1
    · exact mul_assoc g.2 h.2 x.2

/-- Shared original eight-coordinate action of an actual product group. -/
def action {A : Type} [Group A] (rho : A →* Equiv.Perm (Fin 4)) :
    A × C2 →* Equiv.Perm (Fin 8) :=
  points.permCongrHom.toMonoidHom.comp (productAction rho)

theorem action_injective {A : Type} [Group A] (rho : A →* Equiv.Perm (Fin 4))
    (hrho : Function.Injective rho) : Function.Injective (action rho) := by
  intro g h he
  have hp := points.permCongrHom.injective he
  apply Prod.ext
  · apply hrho
    apply Equiv.ext
    intro i
    exact congrArg Prod.fst (congrFun (congrArg Equiv.toFun hp) (i,1))
  · have hb := congrArg Prod.snd (congrFun (congrArg Equiv.toFun hp) (0,1))
    change g.2*1=h.2*1 at hb
    simpa only [mul_one] using hb

private def toRange {A : Type} [Group A] (rho : A →* Equiv.Perm (Fin 4))
    (hrho : Function.Injective rho) : A × C2 ≃* (action rho).range :=
  MulEquiv.ofBijective (action rho).rangeRestrict (by
    constructor
    · intro x y h
      exact action_injective rho hrho (congrArg Subtype.val h)
    · intro y
      obtain ⟨x,hx⟩ := y.property
      exact ⟨x,Subtype.ext hx⟩)

private theorem source_eq_range {A : Type} [Group A] [Finite A] {ι : Type}
    (rho : A →* Equiv.Perm (Fin 4)) (hrho : Function.Injective rho)
    (generators : ι → Equiv.Perm (Fin 8)) (lifts : ι → A × C2)
    (hpoints : ∀ j x, action rho (lifts j) x = generators j x)
    (hcard : Nat.card (Subgroup.closure (Set.range generators)) = Nat.card (A × C2)) :
    Subgroup.closure (Set.range generators) = (action rho).range := by
  have hle : Subgroup.closure (Set.range generators) ≤ (action rho).range := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact ⟨lifts j,Equiv.ext (hpoints j)⟩
  have hrange : Nat.card (action rho).range = Nat.card (A × C2) :=
    Nat.card_congr (toRange rho hrho).toEquiv.symm
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard,hrange])


namespace Alternating
abbrev A := NaturalA4ScalarFourHead.G
abbrev Top := Subgroup.closure (Set.range PrimitiveAffineEightFrameRow0TopCertificate.generators)
private def localPerm : Fin 4 → Equiv.Perm (Fin 4) :=
  ![Equiv.swap 1 3 * Equiv.swap 3 2,NaturalS4.c3,NaturalS4.c1,1]
private theorem local_even_checked : ∀ j : Fin 4, localPerm j ∈ alternatingGroup (Fin 4) := by
  intro j
  change Equiv.Perm.sign (localPerm j)=1
  revert j
  decide +kernel
private def lifts (j : Fin 4) : A × C2 :=
  (⟨localPerm j,local_even_checked j⟩,if j=3 then Multiplicative.ofAdd 1 else 1)
private theorem points_checked : ∀ (j : Fin 4) (x : Fin 8),
    action (alternatingGroup (Fin 4)).subtype (lifts j) x =
      PrimitiveAffineEightFrameRow0TopCertificate.generators j x := by
  decide +kernel
private theorem top_card : Nat.card Top = 24 := by
  letI : Group PrimitiveAffineEightFrameRow0TopCertificate.Source :=
    PrimitiveAffineEightFrameRow0TopCertificate.group
  exact (Nat.card_congr PrimitiveAffineEightFrameRow0TopCertificate.originalEquiv.toEquiv).symm.trans
    PrimitiveAffineEightFrameRow0TopCertificate.source_card
private theorem product_card : Nat.card (A × C2) = 24 := by
  rw [Nat.card_prod]
  have ha : Nat.card A = 12 := by
    change Nat.card (alternatingGroup (Fin 4)) = 12
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have hc : Nat.card C2 = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  rw [ha,hc]

theorem top_eq_range : Top = (action (alternatingGroup (Fin 4)).subtype).range :=
  source_eq_range _ Subtype.val_injective _ lifts points_checked (top_card.trans product_card.symm)

def equiv : Top ≃* A × C2 :=
  (MulEquiv.subgroupCongr top_eq_range).trans
    (toRange (alternatingGroup (Fin 4)).subtype Subtype.val_injective).symm
end Alternating

namespace Symmetric
abbrev Top := Subgroup.closure (Set.range PrimitiveAffineEightFrameRow8TopCertificate.generators)
private def lifts : Fin 5 → Equiv.Perm (Fin 4) × C2 :=
  ![(Equiv.swap 2 3,1),(Equiv.swap 1 3 * Equiv.swap 3 2,1),
    (NaturalS4.c3,1),(NaturalS4.c1,1),(1,Multiplicative.ofAdd 1)]
private theorem points_checked : ∀ (j : Fin 5) (x : Fin 8),
    action (MonoidHom.id _) (lifts j) x =
      PrimitiveAffineEightFrameRow8TopCertificate.generators j x := by
  decide +kernel
private theorem top_card : Nat.card Top = 48 := by
  letI : Group PrimitiveAffineEightFrameRow8TopCertificate.Source :=
    PrimitiveAffineEightFrameRow8TopCertificate.group
  exact (Nat.card_congr PrimitiveAffineEightFrameRow8TopCertificate.originalEquiv.toEquiv).symm.trans
    PrimitiveAffineEightFrameRow8TopCertificate.source_card
private theorem product_card : Nat.card (Equiv.Perm (Fin 4) × C2) = 48 := by
  rw [Nat.card_prod,Nat.card_perm,Nat.card_fin]
  have hc : Nat.card C2 = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  rw [hc]
  norm_num

theorem top_eq_range : Top = (action (MonoidHom.id (Equiv.Perm (Fin 4)))).range :=
  source_eq_range _ Function.injective_id _ lifts points_checked (top_card.trans product_card.symm)

def equiv : Top ≃* Equiv.Perm (Fin 4) × C2 :=
  (MulEquiv.subgroupCongr top_eq_range).trans
    (toRange (MonoidHom.id _) Function.injective_id).symm
end Symmetric

private def matchEquiv (p : PreE7PairActionClass 4)
    (M : DegreeEightCanonicalCatalogue.TransitiveLiteralMatch (preE7PairAction 4 p)) :
    preE7PairAction 4 p ≃* (DegreeTwoPairedEightSharedTops.interface M.index).top :=
  PermutationStabilizerTransport.groupEquiv _ _ M.points M.conjugator M.matched

/-- Actual canonical C2×A4 row, with its original source equivalence. -/
def alternatingRowOfMatch (p : PreE7PairActionClass 4)
    (M : DegreeEightCanonicalCatalogue.TransitiveLiteralMatch (preE7PairAction 4 p))
    (hindex : M.index = (0 : Fin 24)) :
    PublishedDegreeTwoFourPairRow (preE7FourPairNonPairAction p) := by
  have heq : (DegreeTwoPairedEightSharedTops.interface M.index).top = Alternating.Top := by
    rw [hindex]
    rfl
  exact .central (.alternatingFourTimesTwo
    ((matchEquiv p M).trans ((MulEquiv.subgroupCongr heq).trans Alternating.equiv)))

/-- Actual canonical C2×S4 row, with its original source equivalence. -/
def symmetricRowOfMatch (p : PreE7PairActionClass 4)
    (M : DegreeEightCanonicalCatalogue.TransitiveLiteralMatch (preE7PairAction 4 p))
    (hindex : M.index = (5 : Fin 24)) :
    PublishedDegreeTwoFourPairRow (preE7FourPairNonPairAction p) := by
  have heq : (DegreeTwoPairedEightSharedTops.interface M.index).top = Symmetric.Top := by
    rw [hindex]
    rfl
  exact .central (.symmetricFourTimesTwo
    ((matchEquiv p M).trans ((MulEquiv.subgroupCongr heq).trans Symmetric.equiv)))
end SymmetricSubgroupAsymptotics.FourPairCentralProductCanonicalRows
end
