import SymmetricSubgroupAsymptotics.PrimitivePrimeCycleCardinalityDivisibility
import SymmetricSubgroupAsymptotics.SmallIndexPrimitiveCosetAction
import SymmetricSubgroupAsymptotics.SimpleLeastIndexCompositionChart

/-! A finite simple group whose actual proper indices are at least p,
whose order is divisible by the prime p but not by p+1, has no actual
proper index strictly between p and2p. The SAME original coset action
is made primitive by maximality and kept faithful by simplicity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SimplePrimeProperIndexBandExclusion

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem index_eq_prime_or_two_mul_le
    (p : ℕ) (hp : p.Prime)
    (hfloor : ∀ L : Subgroup G, L≠⊤ → p≤L.index)
    (hprime : p ∣ Nat.card G) (hnext : ¬p+1 ∣ Nat.card G)
    (K : Subgroup G) (hK : K≠⊤) : K.index=p ∨ 2*p≤K.index := by
  classical
  by_cases hsmall : K.index<2*p
  · by_cases heq : K.index=p
    · exact Or.inl heq
    · have hlarge : p<K.index := by have hf := hfloor K hK; omega
      letI : Fintype (G ⧸ K) := Fintype.ofFinite _
      letI : MulAction.IsPreprimitive G (G ⧸ K) :=
        SmallIndexPrimitiveCosetAction.coset_isPreprimitive_of_index_lt_twice
          p hfloor K hK hsmall
      let f := MulAction.toPermHom G (G ⧸ K)
      have hf : Function.Injective f :=
        PrimitiveSocleRawStructure.simple_cosetAction_injective K hK
      let P : Subgroup (Equiv.Perm (G ⧸ K)) := f.range
      let q : G →* P := f.rangeRestrict
      let points : (G ⧸ K) →ₑ[q] (G ⧸ K) :=
        { toFun := id, map_smul' := by intros; rfl }
      have hP : MulAction.IsPreprimitive P (G ⧸ K) :=
        MulAction.IsPreprimitive.of_surjective (f:=points) Function.surjective_id
      have hq : Function.Bijective q :=
        ⟨fun _ _ h => hf (congrArg Subtype.val h),f.rangeRestrict_surjective⟩
      have hcard : Nat.card P=Nat.card G :=
        (Nat.card_congr (Equiv.ofBijective q hq)).symm
      have hpP : p ∣ Nat.card P := by rw [hcard]; exact hprime
      letI : Fact p.Prime := ⟨hp⟩
      obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G:=P) p hpP
      have ha' : orderOf (a : Equiv.Perm (G ⧸ K))=p :=
        (orderOf_injective P.subtype Subtype.val_injective a).trans ha
      have hd := PrimitivePrimeCycleCardinalityDivisibility.prime_add_one_dvd_card_of_prime_order
        P hP p hp a.val a.property ha'
        (by simpa only [←K.index_eq_card] using hlarge)
        (by simpa only [←K.index_eq_card] using hsmall)
      rw [hcard] at hd
      exact (hnext hd).elim
  · exact Or.inr (Nat.le_of_not_gt hsmall)

end SymmetricSubgroupAsymptotics.SimplePrimeProperIndexBandExclusion
