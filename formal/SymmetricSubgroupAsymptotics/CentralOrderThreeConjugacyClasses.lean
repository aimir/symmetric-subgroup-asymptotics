import SymmetricSubgroupAsymptotics.CentralInvolutionConjugacyClasses
import SymmetricSubgroupAsymptotics.FiniteActionFibreBurnside
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! A literal central cyclic subgroup of order three acts on the original
conjugacy classes by multiplication. Its actual quotient-class fibres
are precisely these orbits. Burnside gives an exact identity; the full
centre quotient is reached by a surjection, without identifying the
whole centre with the displayed cyclic subgroup. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite
namespace SymmetricSubgroupAsymptotics.CentralOrderThreeConjugacyClasses
open CentralInvolutionConjugacyClasses
variable {G Q : Type*} [Group G] [Group Q]

@[reducible] private def classAction (N : Subgroup G) (hN : N≤Subgroup.center G) :
    MulAction N (ConjClasses G) where
  smul n := translate n.val (hN n.property)
  one_smul c := by
    obtain ⟨x,rfl⟩ := ConjClasses.mk_surjective c
    change ConjClasses.mk ((1:G)*x)=ConjClasses.mk x
    rw [one_mul]
  mul_smul a b c := by
    obtain ⟨x,rfl⟩ := ConjClasses.mk_surjective c
    change ConjClasses.mk ((a:G)*(b:G)*x)=ConjClasses.mk ((a:G)*((b:G)*x))
    rw [mul_assoc]

private theorem translate_congr {a b : G} (ha : a∈Subgroup.center G)
    (hb : b∈Subgroup.center G) (hab : a=b) (c : ConjClasses G) :
    translate a ha c=translate b hb c := by
  subst b
  rfl

/-- The same fixed classes are fixed by either nonidentity element. -/
theorem square_translate_fixed_iff (z : G) (hz : z∈Subgroup.center G)
    (hz3 : z^3=1) (c : ConjClasses G) :
    translate (z^2) ((Subgroup.center G).pow_mem hz 2) c=c ↔ translate z hz c=c := by
  have htwo (d : ConjClasses G) : translate z hz (translate z hz d)=
      translate (z^2) ((Subgroup.center G).pow_mem hz 2) d := by
    obtain ⟨x,rfl⟩ := ConjClasses.mk_surjective d
    change ConjClasses.mk (z*(z*x))=ConjClasses.mk (z^2*x)
    rw [pow_two,mul_assoc]
  have hthree (d : ConjClasses G) : translate z hz (translate z hz (translate z hz d))=d := by
    obtain ⟨x,rfl⟩ := ConjClasses.mk_surjective d
    change ConjClasses.mk (z*(z*(z*x)))=ConjClasses.mk x
    have he : z*(z*(z*x))=z^3*x := by
      simp only [pow_succ,pow_zero,one_mul,mul_assoc]
    rw [he,hz3,one_mul]
  constructor
  · intro h
    have hh := congrArg (translate z hz) h
    rw [←htwo,hthree] at hh
    exact hh.symm
  · intro h
    calc
      translate (z^2) ((Subgroup.center G).pow_mem hz 2) c=
          translate z hz (translate z hz c) := (htwo c).symm
      _=translate z hz c := congrArg (translate z hz) h
      _=c := h

/-- Exact Burnside formula for a surjection with the actual central
order-three cyclic subgroup as kernel. -/
theorem three_class_card_eq [Finite G] (f : G →* Q) (hf : Function.Surjective f)
    (z : G) (hz : z∈Subgroup.center G) (horder : orderOf z=3)
    (hker : ∀ g : G, f g=1 ↔ g∈Subgroup.zpowers z) :
    3*Nat.card (ConjClasses Q)=Nat.card (ConjClasses G)+
      2*Nat.card {c : ConjClasses G // translate z hz c=c} := by
  classical
  letI : Finite Q := Finite.of_surjective f hf
  letI : Finite (ConjClasses G) :=
    Finite.of_surjective (@ConjClasses.mk G _) ConjClasses.mk_surjective
  letI : Finite (ConjClasses Q) :=
    Finite.of_surjective (@ConjClasses.mk Q _) ConjClasses.mk_surjective
  let N := Subgroup.zpowers z
  have hN : N≤Subgroup.center G := Subgroup.zpowers_le.mpr hz
  letI : MulAction N (ConjClasses G) := classAction N hN
  letI : Fintype N := Fintype.ofFinite N
  have hmap (a : N) (c : ConjClasses G) :
      ConjClasses.map f (a • c)=ConjClasses.map f c :=
    map_translate f a.val (hN a.property) ((hker a.val).mpr a.property) c
  have hfibre (c d : ConjClasses G) (he : ConjClasses.map f c=ConjClasses.map f d) :
      ∃ a : N, a • d=c := by
    obtain ⟨x,rfl⟩ := ConjClasses.mk_surjective c
    obtain ⟨y,rfl⟩ := ConjClasses.mk_surjective d
    obtain ⟨q,hq⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp he)
    obtain ⟨g,hg⟩ := hf q
    have hm : f ((g*x*g⁻¹)*y⁻¹)=1 := by
      rw [map_mul,map_mul,map_mul,map_inv,map_inv,hg,hq,mul_inv_cancel]
    let a : N := ⟨(g*x*g⁻¹)*y⁻¹,(hker _).mp hm⟩
    refine ⟨a,?_⟩
    change ConjClasses.mk ((a:G)*y)=ConjClasses.mk x
    apply (ConjClasses.mk_eq_mk_iff_isConj.mpr _).symm
    exact isConj_iff.mpr ⟨g,(mul_inv_eq_iff_eq_mul.mp (rfl :
      (g*x*g⁻¹)*y⁻¹=(a:G)))⟩
  have hburn := FiniteActionFibreBurnside.card_mul_group_eq_sum_fixed
    (ConjClasses.map f) (ConjClasses.map_surjective hf) hmap hfibre
  have hcardN : Nat.card N=3 := by
    calc
      Nat.card N=Nat.card (Fin (orderOf z)) :=
        (Nat.card_congr (finEquivZPowers (isOfFinOrder_of_finite z))).symm
      _=orderOf z := Nat.card_fin _
      _=3 := horder
  let e : Fin 3 ≃ N := (finCongr horder.symm).trans
    (finEquivZPowers (isOfFinOrder_of_finite z))
  have he (i : Fin 3) : ((e i : N):G)=z^(i.val) := rfl
  have hzero : Nat.card (MulAction.fixedBy (ConjClasses G) (e 0))=
      Nat.card (ConjClasses G) := by
    have he0 : e 0=1 := Subtype.ext ((he (0 : Fin 3)).trans (pow_zero z))
    rw [he0]
    exact Nat.card_congr
      { toFun := Subtype.val
        invFun := fun c => ⟨c,one_smul N c⟩
        left_inv := fun _ => Subtype.ext rfl
        right_inv := fun _ => rfl }
  have hone : Nat.card (MulAction.fixedBy (ConjClasses G) (e 1))=
      Nat.card {c : ConjClasses G // translate z hz c=c} := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro c
    change translate ((e 1 : N):G) _ c=c ↔ translate z hz c=c
    have he1 : ((e 1 : N):G)=z := (he (1 : Fin 3)).trans (pow_one z)
    rw [translate_congr _ hz he1 c]
  have htwo : Nat.card (MulAction.fixedBy (ConjClasses G) (e 2))=
      Nat.card {c : ConjClasses G // translate z hz c=c} := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro c
    change translate ((e 2 : N):G) _ c=c ↔ translate z hz c=c
    rw [translate_congr _ ((Subgroup.center G).pow_mem hz 2) (he (2 : Fin 3)) c]
    exact square_translate_fixed_iff z hz
      (by simpa only [horder] using pow_orderOf_eq_one z) c
  have hsum : (∑ a : N, Nat.card (MulAction.fixedBy (ConjClasses G) a))=
      Nat.card (ConjClasses G)+2*Nat.card {c : ConjClasses G // translate z hz c=c} := by
    rw [←e.sum_comp (fun a : N => Nat.card (MulAction.fixedBy (ConjClasses G) a)),
      Fin.sum_univ_three,hzero,hone,htwo]
    omega
  calc
    3*Nat.card (ConjClasses Q)=Nat.card (ConjClasses Q)*Nat.card N := by rw [hcardN]; omega
    _=∑ a : N, Nat.card (MulAction.fixedBy (ConjClasses G) a) := hburn
    _=_ := hsum

/-- The exact formula for the actual displayed quotient subgroup. -/
theorem quotient_class_formula [Finite G] (z : G) (hz : z∈Subgroup.center G)
    (horder : orderOf z=3) (N : Subgroup G) [N.Normal]
    (hN : N=Subgroup.zpowers z) :
    3*Nat.card (ConjClasses (G ⧸ N))=Nat.card (ConjClasses G)+
      2*Nat.card {c : ConjClasses G // translate z hz c=c} := by
  apply three_class_card_eq (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    z hz horder
  intro g
  change (g : G ⧸ N)=1 ↔ g∈Subgroup.zpowers z
  exact (QuotientGroup.eq_one_iff g).trans (by rw [hN])

/-- A fixed-class upper bound yields the requested quotient bound,
retaining the same literal central cyclic subgroup. -/
theorem quotient_class_bound [Finite G] (z : G) (hz : z∈Subgroup.center G)
    (horder : orderOf z=3) (N : Subgroup G) [N.Normal]
    (hN : N=Subgroup.zpowers z) (F : ℕ)
    (hfixed : Nat.card {c : ConjClasses G // translate z hz c=c}≤F) :
    3*Nat.card (ConjClasses (G ⧸ N))≤Nat.card (ConjClasses G)+2*F := by
  rw [quotient_class_formula z hz horder N hN]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 hfixed) _

/-- Passing to the full centre quotient uses only its genuine
surjective map from the displayed cyclic quotient. -/
theorem central_quotient_class_bound [Finite G] (z : G) (hz : z∈Subgroup.center G)
    (horder : orderOf z=3) (F : ℕ)
    (hfixed : Nat.card {c : ConjClasses G // translate z hz c=c}≤F) :
    3*Nat.card (ConjClasses (G ⧸ Subgroup.center G))≤Nat.card (ConjClasses G)+2*F := by
  let N := Subgroup.zpowers z
  have hN : N≤Subgroup.center G := Subgroup.zpowers_le.mpr hz
  letI : N.Normal := ⟨fun a ha g => by
    have hc := Subgroup.mem_center_iff.mp (hN ha) g
    simpa only [hc,mul_assoc,mul_inv_cancel,mul_one] using ha⟩
  let f := QuotientGroup.mk' (Subgroup.center G)
  have hn : N≤f.ker := by
    intro a ha
    exact (QuotientGroup.eq_one_iff a).mpr (hN ha)
  let q : G ⧸ N →* G ⧸ Subgroup.center G := QuotientGroup.lift N f hn
  have hq : Function.Surjective q :=
    QuotientGroup.lift_surjective_of_surjective N f (QuotientGroup.mk'_surjective _) hn
  letI : Finite (ConjClasses (G ⧸ N)) := Finite.of_surjective
    (@ConjClasses.mk (G ⧸ N) _) ConjClasses.mk_surjective
  have hb := Nat.card_le_card_of_surjective (ConjClasses.map q) (ConjClasses.map_surjective hq)
  exact (Nat.mul_le_mul_left 3 hb).trans (quotient_class_bound z hz horder N rfl F hfixed)

end SymmetricSubgroupAsymptotics.CentralOrderThreeConjugacyClasses
