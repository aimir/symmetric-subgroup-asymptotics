import SymmetricSubgroupAsymptotics.PrimeIndexAbelianCentralizers
import Mathlib.GroupTheory.Coset.Card

/-! Outside centralizers in a finite prime-index extension have the
FULL quotient as image, because they contain the outside element itself.
Their actual kernel is its fixed subgroup in N. No complement or order-p
lift is required, and the first cardinality theorem does not assume N
abelian. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimeIndexOutsideCentralizerCard
open PrimeIndexAbelianCentralizers
variable {G : Type*} [Group G]

def partnerEquivCentralizer (x : G) : {y : G // Commute x y}≃Subgroup.centralizer {x} where
  toFun y := ⟨y.val,Subgroup.mem_centralizer_singleton_iff.mpr y.property.eq.symm⟩
  invFun y := ⟨y.val,(Subgroup.mem_centralizer_singleton_iff.mp y.property).symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem outside_centralizer_card [Finite G] (N : Subgroup G) [N.Normal]
    (p : ℕ) (hp : p.Prime) (hindex : N.index=p) (x : G) (hx : x∉N) :
    Nat.card (Subgroup.centralizer {x})=p*Nat.card (fixedKernel N x) := by
  let C : Subgroup G := Subgroup.centralizer {x}
  let q : C→*G⧸N := (QuotientGroup.mk' N).comp C.subtype
  have hxC : x∈C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  let a : q.range := ⟨q ⟨x,hxC⟩,⟨⟨x,hxC⟩,rfl⟩⟩
  have ha : a≠1 := by
    intro he
    have hh := congrArg (fun z : q.range=>z.val) he
    change QuotientGroup.mk' N x=1 at hh
    exact hx ((QuotientGroup.eq_one_iff x).mp hh)
  letI : Nontrivial q.range := nontrivial_of_ne a 1 ha
  have hd : Nat.card q.range∣p := by
    have hh := q.range.card_subgroup_dvd_card
    change Nat.card q.range∣N.index at hh
    rwa [hindex] at hh
  have hqcard : Nat.card q.range=p :=
    ((Nat.dvd_prime hp).mp hd).resolve_left (Nat.ne_of_gt (Finite.one_lt_card (α:=q.range)))
  let e : q.ker≃*fixedKernel N x :=
    { toFun := fun y=>⟨⟨y.val.val,(QuotientGroup.eq_one_iff y.val.val).mp y.property⟩,y.val.property⟩
      invFun := fun y=>⟨⟨y.val.val,y.property⟩,(QuotientGroup.eq_one_iff y.val.val).mpr y.val.property⟩
      left_inv := fun _=>rfl
      right_inv := fun _=>rfl
      map_mul' := fun _ _=>rfl }
  have hker : Nat.card q.ker=Nat.card (fixedKernel N x) := Nat.card_congr e.toEquiv
  have hC : Nat.card C=Nat.card q.ker*Nat.card q.range := by
    simpa only [Subgroup.index_ker] using q.ker.card_mul_index.symm
  change Nat.card C=p*Nat.card (fixedKernel N x)
  rw [hC,hker,hqcard]
  exact Nat.mul_comm _ _

theorem outside_centralizer_card_abelian [Finite G] (N : Subgroup G) [N.Normal]
    [IsMulCommutative N] (p : ℕ) (hp : p.Prime) (hindex : N.index=p)
    (x : G) (hx : x∉N) :
    Nat.card (Subgroup.centralizer {x})=p*Nat.card (centralKernel N) := by
  rw [outside_centralizer_card N p hp hindex x hx,fixedKernel_eq_centralKernel N p hp hindex x hx]

end SymmetricSubgroupAsymptotics.PrimeIndexOutsideCentralizerCard
