import SymmetricSubgroupAsymptotics.NormalOrbitFibreCoarsening
import SymmetricSubgroupAsymptotics.SmallBinaryFrattiniCharacteristicLayer
import SymmetricSubgroupAsymptotics.PrimitiveAffineBinarySmallClassBound
import SymmetricSubgroupAsymptotics.OriginalMinimalBlockComponentTransport
import SymmetricSubgroupAsymptotics.PrimitiveTopSmallFibreClassBudget
import SymmetricSubgroupAsymptotics.BinaryParabolicTopSmallFibreNumerics
import SymmetricSubgroupAsymptotics.FrattiniAffineSmallClassBound
import Mathlib.GroupTheory.GroupAction.ConjAct

/-! Actual order-two characteristic translations yield a genuine
six-by-four coarsening of the original ternary/eight action. The class
conclusion uses only strict-smaller GENERAL permutation IH. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.RegularAffineEightTernaryCoarsening

private theorem regular_subgroup_orbit_card
    {G X : Type} [Group G] [MulAction G X]
    (P : PrimitiveAffineProfile G X) (Z : Subgroup G) (hZ : Z≤P.V) (x : X) :
    Nat.card (MulAction.orbit Z x)=Nat.card Z := by
  let f : Z → MulAction.orbit Z x := fun z => ⟨z • x,⟨z,rfl⟩⟩
  have hf : Function.Injective f := by
    intro z w he
    apply Subtype.ext
    have hp : (⟨z.val,hZ z.property⟩ : P.V)=(⟨w.val,hZ w.property⟩ : P.V) :=
      (P.pointEquiv x).injective (congrArg Subtype.val he)
    exact congrArg (fun v : P.V => v.val) hp
  have hs : Function.Surjective f := by
    rintro ⟨y,⟨z,hz⟩⟩
    exact ⟨z,Subtype.ext hz⟩
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hf,hs⟩)).symm

private theorem comap_orbit_eq {A G X : Type} [Group A] [Group G]
    [MulAction A X] [MulAction G X] (r : A →* G) (hr : Function.Surjective r)
    (hact : ∀ (a : A) (x : X), r a • x=a • x) (Z : Subgroup G) (x : X) :
    MulAction.orbit (Z.comap r) x=MulAction.orbit Z x := by
  ext y
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨⟨r a.val,a.property⟩,?_⟩
    exact (hact a.val x).trans ha
  · rintro ⟨z,hz⟩
    obtain ⟨a,ha⟩ := hr z.val
    have hamem : a∈Z.comap r := by
      change r a∈Z
      rw [ha]
      exact z.property
    refine ⟨⟨a,hamem⟩,?_⟩
    calc
      a • x=r a • x := (hact a x).symm
      _=z.val • x := by rw [ha]
      _=y := hz

end SymmetricSubgroupAsymptotics.RegularAffineEightTernaryCoarsening

namespace SymmetricSubgroupAsymptotics.OriginalMinimalBlock
open RegularAffineEightTernaryCoarsening

variable {A Ω : Type} [Group A] [MulAction A Ω] [MulAction.IsPretransitive A Ω]
    [Finite A] [Finite Ω] [FaithfulSMul A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A:=A) ω₀)

theorem class_cube_le_of_ternary_eight_affine_rank_le_two
    (hc : Nat.card D.Fibre=3) (P : PrimitiveAffineProfile D.Top D.Points)
    (hdegree : Nat.card D.Points=8)
    (hr : Module.finrank (ZMod 2) (PrimeCharacters 2 P.V)≤2)
    (hSmaller : ∀ m : ℕ, m < (Nat.card Ω) → 4 ≤ m →
      ∀ L : Subgroup (Equiv.Perm (Fin m)), Nat.card (ConjClasses L)^3≤5^(m-1)) :
    Nat.card (ConjClasses A)^3≤5^(Nat.card Ω-1) := by
  letI : Nontrivial D.Points := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  letI : Fact P.p.Prime := ⟨P.p_prime⟩
  have hp : P.p=2 :=
    PrimitiveAffineBinarySmallClassBound.profile_prime_eq_two_of_degree_pow P D.base 3
      (by simpa only [show (2:ℕ)^3=8 by decide] using hdegree)
  have hV : Nat.card P.V=8 := (P.card_eq D.base).trans hdegree
  have hVtwo : IsPGroup 2 P.V := by simpa only [hp] using P.V_pgroup
  obtain ⟨Z,hZ,hZcard⟩ :=
    SmallBinaryFrattiniCharacteristicLayer.exists_characteristic_two_of_rank_le_two hVtwo hV hr
  letI : Z.Characteristic := hZ
  let W : Subgroup D.Top := Z.map P.V.subtype
  letI : W.Normal := inferInstance
  have hWV : W≤P.V := by
    rintro w ⟨z,_,rfl⟩
    exact z.property
  have hWcard : Nat.card W=2 :=
    (Nat.card_congr (Z.equivMapOfInjective P.V.subtype Subtype.val_injective).toEquiv).symm.trans hZcard
  let r : A →* D.Top := D.topMap.rangeRestrict
  let K : Subgroup A := W.comap r
  letI : K.Normal := inferInstance
  have hact (a : A) (x : D.Points) : r a • x=a • x := rfl
  have hKcard (x : D.Points) : Nat.card (MulAction.orbit K x)=2 := by
    have ho : MulAction.orbit K x=MulAction.orbit W x :=
      comap_orbit_eq r D.topMap.rangeRestrict_surjective hact W x
    rw [ho]
    exact (regular_subgroup_orbit_card P W hWV x).trans hWcard
  have hprod := NormalOrbitFibreCoarsening.blocks_card_mul K D.base 2 hKcard
  rw [hdegree] at hprod
  have hfour : 4≤Nat.card (NormalOrbitFibreCoarsening.Blocks K D.base) := by omega
  exact NormalOrbitFibreCoarsening.exact_exponent_large_block_cube_step K D.base
    D.map D.map_equivariant 3 2 (by decide) hfour
    (fun x => (D.fibre_card_at x).trans hc) hKcard hSmaller

private theorem eight_rank_three_subgroup_bound
    (P : PrimitiveAffineProfile D.Top D.Points) (hdegree : Nat.card D.Points=8)
    (hr : Module.finrank (ZMod 2) (PrimeCharacters 2 P.V)=3)
    (L : Subgroup D.Top) : Nat.card (ConjClasses L)≤24 := by
  letI : Nontrivial D.Points := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hp : P.p=2 :=
    PrimitiveAffineBinarySmallClassBound.profile_prime_eq_two_of_degree_pow P D.base 3
      (by simpa only [show (2:ℕ)^3=8 by decide] using hdegree)
  have hV : Nat.card P.V=2^3 := by
    simpa only [show (2:ℕ)^3=8 by decide] using (P.card_eq D.base).trans hdegree
  have hVtwo : IsPGroup 2 P.V := by simpa only [hp] using P.V_pgroup
  let e := P.semidirectEquiv D.base
  let R := L.map e.symm.toMonoidHom
  let a : L≃*R := e.symm.subgroupMap L
  letI : Finite R := Finite.of_equiv L a.toEquiv
  have hc : Nat.card (ConjClasses L)≤Nat.card (ConjClasses R) :=
    (conjugacyClass_card_congr (G:=L) (H:=R) a).le
  have hb := FrattiniAffineSmallClassBound.binary_rank_bound 2 P.V
    (P.complementAction D.base) rfl hVtwo (P.complementAction_injective D.base)
    3 (by decide) hV R
  simpa only [hr,Nat.sub_self,zero_mul,pow_zero,one_mul,
    ElementaryPrimeHolomorphClassBound.binaryBudget] using hc.trans hb

theorem class_cube_le_of_ternary_eight_affine_top
    (hc : Nat.card D.Fibre=3) (P : PrimitiveAffineProfile D.Top D.Points)
    (hdegree : Nat.card D.Points=8)
    (hSmaller : ∀ m : ℕ, m < (Nat.card Ω) → 4 ≤ m →
      ∀ L : Subgroup (Equiv.Perm (Fin m)), Nat.card (ConjClasses L)^3≤5^(m-1)) :
    Nat.card (ConjClasses A)^3≤5^(Nat.card Ω-1) := by
  have hV : Nat.card P.V=2^3 := by
    simpa only [show (2:ℕ)^3=8 by decide] using (P.card_eq D.base).trans hdegree
  have hr := PrimeFrattiniCardinality.rank_le_exponent 2 P.V 3 hV
  by_cases hr3 : Module.finrank (ZMod 2) (PrimeCharacters 2 P.V)=3
  · have htop : ∀ L : Subgroup D.Top, L.IsSubnormal → Nat.card (ConjClasses L)≤24 :=
      fun L _ => eight_rank_three_subgroup_bound D P hdegree hr3 L
    have hbinary : (((24:ℕ)+1)*2^(Nat.card D.Points-2))^3≤5^(2*Nat.card D.Points-1) := by
      simpa [hdegree,PrimitiveAffineBinaryParabolicClassBound.classBudget] using
        BinaryParabolicTopSmallFibreNumerics.binary_unsigned_capacity 8 (Or.inl rfl)
    have hternary : (3^Nat.card D.Points*(24:ℕ))^3≤5^(3*Nat.card D.Points-1) := by
      simpa [hdegree,PrimitiveAffineBinaryParabolicClassBound.classBudget] using
        BinaryParabolicTopSmallFibreNumerics.ternary_capacity 8 (Or.inl rfl)
    have hh := PrimitiveTopSmallFibreClassBudget.subnormal_class_cube_le_of_regular_top
      D.map D.map_equivariant 3 (Or.inr rfl)
      (fun x => (D.fibre_card_at x).trans hc) P (by omega) 24 (by decide) htop
      hbinary hternary ⊤ (Subgroup.Normal.isSubnormal inferInstance)
    have he := conjugacyClass_card_congr
      (Subgroup.topEquiv : (⊤ : Subgroup A) ≃* A)
    rwa [he] at hh
  · exact D.class_cube_le_of_ternary_eight_affine_rank_le_two hc P hdegree
      (by omega) hSmaller

end SymmetricSubgroupAsymptotics.OriginalMinimalBlock
