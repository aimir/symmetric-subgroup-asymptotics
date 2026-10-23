import SymmetricSubgroupAsymptotics.SquareZeroLinearBasisPairs
import Mathlib.FieldTheory.Finiteness

/-! A rank-one square-zero binary operator has a constrained centralizer
chart. The first value belongs to one kernel coset; all remaining kernel
basis images avoid the two-element image line. This gives the uniform
bound k*(k-2)^(dim(kernel)-1), without counting a matrix group. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.RankOneSquareZeroCentralizer
open BinaryLinearQuadraticDichotomy

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem range_scalar (N : V →ₗ[K] V) (hr : Module.finrank K N.range=1)
    (v : V) (hv : N v ≠ 0) (x : V) (hx : x ∈ N.range) :
    ∃a : K, a • N v=x := by
  let w : N.range := ⟨N v,⟨v,rfl⟩⟩
  have hw : w ≠ 0 := fun h => hv (congrArg Subtype.val h)
  obtain ⟨a,ha⟩ := exists_smul_eq_of_finrank_eq_one hr hw (⟨x,hx⟩ : N.range)
  exact ⟨a,congrArg Subtype.val ha⟩

theorem commuting_fixes_image (hK : Nat.card K=2) (N : V →ₗ[K] V)
    (hr : Module.finrank K N.range=1) (v : V) (hv : N v ≠ 0)
    (a : V ≃ₗ[K] V) (ha : ∀x : V, N (a x)=a (N x)) : a (N v)=N v := by
  obtain ⟨c,hc⟩ := range_scalar N hr v hv (a (N v)) ⟨a v,ha v⟩
  have hc0 : c ≠ 0 := by
    intro h0
    have hz : a (N v)=0 := by simpa only [h0,zero_smul] using hc.symm
    exact hv (a.injective (hz.trans (map_zero a).symm))
  have hc1 : c=1 := (scalar_eq_zero_or_one hK c).resolve_left hc0
  simpa only [hc1,one_smul] using hc.symm

def fiberEquivKer (N : V →ₗ[K] V) (v : V) :
    {x : V // N x=N v} ≃ N.ker where
  toFun x := ⟨x.val-v,by change N (x.val-v)=0; rw [map_sub,x.property,sub_self]⟩
  invFun x := ⟨v+x.val,by rw [map_add,x.property,add_zero]⟩
  left_inv x := by apply Subtype.ext; dsimp; abel
  right_inv x := by apply Subtype.ext; dsimp; abel

theorem card_le [Finite V] (hK : Nat.card K=2) (N : V →ₗ[K] V)
    (hN : ∀v : V, N (N v)=0) (hr : Module.finrank K N.range=1)
    (e : V ≃ₗ[K] V) (he : ∀v : V, e v=v+N v) :
    Nat.card {a : V ≃ₗ[K] V // Commute e a} ≤
      Nat.card N.ker * (Nat.card N.ker-2)^(Module.finrank K N.ker-1) := by
  letI : FiniteDimensional K V := Module.Finite.of_finite
  obtain ⟨v,hv⟩ : ∃v : V, N v ≠ 0 := by
    by_contra hn
    have hall : ∀v : V, N v=0 := by simpa only [not_exists,not_not] using hn
    have hz : N=0 := by ext v; exact hall v
    have hdim : Module.finrank K N.range=0 := by
      rw [LinearMap.range_eq_bot.mpr hz]
      exact finrank_bot K V
    omega
  let W := N.ker
  let w : W := ⟨N v,hN v⟩
  have hw : w ≠ 0 := fun h => hv (congrArg Subtype.val h)
  have hs : LinearIndepOn K id ({w} : Set W) := LinearIndepOn.singleton hw
  let I := hs.extend (Set.subset_univ _)
  let b : Module.Basis I K W := Module.Basis.extend hs
  let i : I := ⟨w,hs.subset_extend _ (by simp)⟩
  have hi : b i=w := Module.Basis.extend_apply_self hs i
  let J := {j : I // j ≠ i}
  let T := {x : W // x ≠ 0 ∧ x ≠ w}
  have hcomm (a : {a : V ≃ₗ[K] V // Commute e a}) (x : V) :
      N (a.val x)=a.val (N x) := by
    have hh := congrArg (fun f : V ≃ₗ[K] V => f x) a.property
    change e (a.val x)=a.val (e x) at hh
    simp only [he,map_add] at hh
    exact add_left_cancel hh
  have hfix (a : {a : V ≃ₗ[K] V // Commute e a}) : a.val (N v)=N v :=
    commuting_fixes_image hK N hr v hv a.val (hcomm a)
  let image (a : {a : V ≃ₗ[K] V // Commute e a}) (j : J) : W :=
    ⟨a.val ((b j.val : W) : V),by
      change N (a.val ((b j.val : W) : V))=0
      rw [hcomm a]
      change a.val (N ((b j.val : W) : V))=0
      rw [(b j.val).property,map_zero]⟩
  have himage0 (a : {a : V ≃ₗ[K] V // Commute e a}) (j : J) : image a j ≠ 0 := by
    intro hz
    have hz' : a.val ((b j.val : W) : V)=0 := congrArg Subtype.val hz
    have hb0 : b j.val=0 := Subtype.ext (a.val.injective (hz'.trans (map_zero a.val).symm))
    exact b.ne_zero j.val hb0
  have himagew (a : {a : V ≃ₗ[K] V // Commute e a}) (j : J) : image a j ≠ w := by
    intro hz
    have hz' : a.val ((b j.val : W) : V)=N v := congrArg Subtype.val hz
    have hbw : b j.val=w := Subtype.ext (a.val.injective (hz'.trans (hfix a).symm))
    exact j.property (b.injective (hbw.trans hi.symm))
  let chart : {a : V ≃ₗ[K] V // Commute e a} →
      {x : V // N x=N v} × (J → T) := fun a =>
    (⟨a.val v,(hcomm a v).trans (hfix a)⟩,
      fun j => ⟨image a j,himage0 a j,himagew a j⟩)
  have hchart : Function.Injective chart := by
    intro a a' haa
    have hval : a.val v=a'.val v :=
      congrArg (fun z : {x : V // N x=N v} × (J → T) => z.1.val) haa
    have hker : ∀x : W, a.val (x : V)=a'.val (x : V) := by
      have hh : a.val.toLinearMap.comp W.subtype=a'.val.toLinearMap.comp W.subtype := by
        apply b.ext
        intro j
        change a.val ((b j : W) : V)=a'.val ((b j : W) : V)
        by_cases hj : j=i
        · subst j
          rw [hi]
          exact (hfix a).trans (hfix a').symm
        · exact congrArg (fun z : {x : V // N x=N v} × (J → T) =>
            ((z.2 ⟨j,hj⟩).val : V)) haa
      intro x
      exact DFunLike.congr_fun hh x
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    obtain ⟨c,hc⟩ := range_scalar N hr v hv (N x) ⟨x,rfl⟩
    let y : W := ⟨x-c • v,by
      change N (x-c • v)=0
      rw [map_sub,map_smul,hc,sub_self]⟩
    have hh := hker y
    change a.val (x-c • v)=a'.val (x-c • v) at hh
    rw [map_sub,map_sub,map_smul,map_smul,hval] at hh
    simpa only [sub_add_cancel] using congrArg (fun z : V => z+c • a'.val v) hh
  letI : Fintype I := Fintype.ofFinite I
  letI : Fintype W := Fintype.ofFinite W
  have hJ : Nat.card J=Nat.card I-1 := by
    simp only [J,Nat.card_eq_fintype_card]
    simp [Fintype.card_subtype_compl]
  have hT : Nat.card T=Nat.card W-2 := by
    let t : T ≃ ↥(({0,w} : Finset W)ᶜ) := {
      toFun := fun x => ⟨x.val,by simpa using x.property⟩
      invFun := fun x => ⟨x.val,by simpa using x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    rw [Nat.card_congr t,Nat.card_eq_fintype_card,Fintype.card_coe,
      Finset.card_compl,Finset.card_pair hw.symm,Nat.card_eq_fintype_card]
  have hd : Module.finrank K W=Nat.card I := by
    simpa only [Nat.card_eq_fintype_card] using Module.finrank_eq_card_basis b
  calc
    Nat.card {a : V ≃ₗ[K] V // Commute e a} ≤
        Nat.card ({x : V // N x=N v} × (J → T)) :=
      Nat.card_le_card_of_injective chart hchart
    _ = Nat.card N.ker*(Nat.card N.ker-2)^(Module.finrank K N.ker-1) := by
      rw [Nat.card_prod,Nat.card_fun,Nat.card_congr (fiberEquivKer N v),hT,hJ,←hd]

end SymmetricSubgroupAsymptotics.RankOneSquareZeroCentralizer
