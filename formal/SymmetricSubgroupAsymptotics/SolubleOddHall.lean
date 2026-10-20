import SymmetricSubgroupAsymptotics.NormalTwoKernelOddHall
import SymmetricSubgroupAsymptotics.BinaryBySymmetricThree

/-!
# Odd Hall subgroups of finite soluble groups

This proves the literal order condition required by the soluble Tracey
input. Induction on the group order chooses a minimal normal subgroup.
It is abelian, hence either a binary group or has odd order. An odd Hall
subgroup of the quotient pulls back directly in the odd case. In the
binary case Schur--Zassenhaus splits the binary kernel in that pullback.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

private theorem oddHall_pullback_of_odd_kernel
    {G : Type} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (hNodd : ¬ 2 ∣ Nat.card N)
    (Pq : Subgroup (G ⧸ N)) (hPq : IsTwoComplement Pq) :
    IsTwoComplement (Pq.comap (QuotientGroup.mk' N)) := by
  have hNcompl : ordCompl[2] (Nat.card N) = Nat.card N :=
    (Nat.ordCompl_eq_self_iff_zero_or_not_dvd
      (Nat.card N) Nat.prime_two).mpr (Or.inr hNodd)
  have hGcard := N.card_eq_card_quotient_mul_card_subgroup
  have hPqSetCard : Nat.card (Pq : Set (G ⧸ N)) =
      ordCompl[2] (Nat.card (G ⧸ N)) := hPq
  change Nat.card ((QuotientGroup.mk : G → G ⧸ N) ⁻¹' (Pq : Set (G ⧸ N))) =
    ordCompl[2] (Nat.card G)
  rw [QuotientGroup.card_preimage_mk, hPqSetCard, hGcard,
    Nat.ordCompl_mul, hNcompl]
  exact Nat.mul_comm _ _

private theorem exists_oddHall_of_binary_kernel
    {G : Type} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal]
    (hN : ∃ a : ℕ, Nat.card N = 2 ^ a)
    (Pq : Subgroup (G ⧸ N)) (hPq : IsTwoComplement Pq) :
    ∃ P : Subgroup G, IsTwoComplement P := by
  let Q := G ⧸ N
  let pi : G →* Q := QuotientGroup.mk' N
  let T : Subgroup G := Pq.comap pi
  let piT : T →* Pq := {
    toFun := fun t ↦ ⟨pi t.1, t.2⟩
    map_one' := by ext; simp [pi]
    map_mul' := by intro x y; ext; simp [pi] }
  have hpiT : Function.Surjective piT := by
    intro q
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N q.1
    refine ⟨⟨g, ?_⟩, ?_⟩
    · change pi g ∈ Pq
      simpa only [pi, hg] using q.2
    · apply Subtype.ext
      exact hg
  let K : Subgroup T := piT.ker
  letI : K.Normal := inferInstance
  have hKcard : Nat.card K = Nat.card N := by
    let e : N →* K := {
      toFun := fun x ↦ ⟨⟨x.1, by
        change pi x.1 ∈ Pq
        have hx : pi x.1 = 1 := (QuotientGroup.eq_one_iff x.1).mpr x.2
        rw [hx]
        exact Pq.one_mem⟩, by
          apply Subtype.ext
          exact (QuotientGroup.eq_one_iff x.1).mpr x.2⟩
      map_one' := by ext; rfl
      map_mul' := by intro x y; ext; rfl }
    have heinj : Function.Injective e := by
      intro x y hxy
      exact Subtype.ext (congrArg (fun z : K ↦ (z.1.1 : G)) hxy)
    have hesurj : Function.Surjective e := by
      intro k
      refine ⟨⟨k.1.1, ?_⟩, ?_⟩
      · have hkoneQ : pi k.1.1 = 1 := congrArg Subtype.val k.2
        exact (QuotientGroup.eq_one_iff k.1.1).mp hkoneQ
      · apply Subtype.ext
        rfl
    exact Nat.card_congr (MulEquiv.ofBijective e ⟨heinj, hesurj⟩).toEquiv.symm
  have hKindex : K.index = Nat.card Pq := by
    change piT.ker.index = Nat.card Pq
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hpiT, Subgroup.card_top]
  obtain ⟨a, ha⟩ := hN
  have hcop : Nat.Coprime (Nat.card K) K.index := by
    rw [hKcard, ha, hKindex, hPq]
    exact (Nat.coprime_ordCompl Nat.prime_two
      (Nat.card_pos (α := Q)).ne').pow_left a
  obtain ⟨H, hKH⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  let P : Subgroup G := H.map T.subtype
  have hPcard : Nat.card P = Nat.card Pq := by
    calc
      Nat.card P = Nat.card H := by
        exact Nat.card_congr
          (H.equivMapOfInjective T.subtype T.subtype_injective).toEquiv.symm
      _ = K.index := hKH.card_right
      _ = Nat.card Pq := hKindex
  refine ⟨P, ?_⟩
  change Nat.card P = ordCompl[2] (Nat.card G)
  rw [hPcard, hPq]
  have hGcard := N.card_eq_card_quotient_mul_card_subgroup
  rw [hGcard, Nat.ordCompl_mul, ha,
    Nat.ordCompl_self_pow Nat.prime_two, mul_one]

/-- Every finite soluble group has an actual subgroup whose order is the
odd part of its order. The subgroup is the `2`-complement appearing in the
soluble induced-module theorem. -/
theorem exists_isTwoComplement_of_isSolvable
    {G : Type} [Group G] [Finite G] [IsSolvable G] :
    ∃ P : Subgroup G, IsTwoComplement P := by
  suffices hall : ∀ n : ℕ, ∀ (H : Type) [Group H] [Finite H] [IsSolvable H],
      Nat.card H = n → ∃ P : Subgroup H, IsTwoComplement P by
    exact hall (Nat.card G) G rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro H _ _ _ hcard
    by_cases h1 : Nat.card H = 1
    · refine ⟨⊤, ?_⟩
      change Nat.card (⊤ : Subgroup H) = ordCompl[2] (Nat.card H)
      rw [Subgroup.card_top, h1]
      exact (Nat.ordCompl_self_pow (k := 0) Nat.prime_two).symm
    have htop : (⊤ : Subgroup H) ≠ ⊥ := by
      intro heq
      apply h1
      simpa only [Subgroup.card_top, Subgroup.card_bot] using
        congrArg (fun K : Subgroup H => Nat.card K) heq
    let good : Subgroup H → Prop := fun N => N.Normal ∧ N ≠ ⊥
    obtain ⟨N, _hNtop, hmin⟩ :=
      Finite.exists_le_minimal (p := good) (a := (⊤ : Subgroup H))
        (show good ⊤ from ⟨inferInstance, htop⟩)
    have hN : IsMinimalNormalSubgroup N := by
      refine ⟨hmin.1.1, hmin.1.2, ?_⟩
      intro K hKnormal hKne hKN
      exact hmin.eq_of_le ⟨hKnormal, hKne⟩ hKN
    letI : N.Normal := hN.1
    have hquot : Nat.card (H ⧸ N) < n := by
      rw [← hcard, N.card_eq_card_quotient_mul_card_subgroup]
      exact lt_mul_of_one_lt_right Nat.card_pos (N.one_lt_card_iff_ne_bot.mpr hN.2.1)
    obtain ⟨Pq, hPq⟩ := ih (Nat.card (H ⧸ N)) hquot (H ⧸ N) rfl
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    by_cases hbinary : IsPGroup 2 N
    · exact exists_oddHall_of_binary_kernel N hbinary.exists_card_eq Pq hPq
    · have hcomm := minimalNormal_isMulCommutative_of_isSolvable N hN
      have hcop := abelianMinimalNormal_card_coprime_of_not_isPGroup
        2 N hN hcomm hbinary
      have hodd : ¬ 2 ∣ Nat.card N :=
        Nat.prime_two.coprime_iff_not_dvd.mp hcop.symm
      exact ⟨Pq.comap (QuotientGroup.mk' N),
        oddHall_pullback_of_odd_kernel N hodd Pq hPq⟩

end SymmetricSubgroupAsymptotics

end
