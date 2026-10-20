import SymmetricSubgroupAsymptotics.NormalPGroupOrbitTransversal
import SymmetricSubgroupAsymptotics.MinimalNormalCompositionCharts
import SymmetricSubgroupAsymptotics.BinaryBySymmetricThree

/-! Every actual point stabilizer in a finite soluble group has a
triangular prime-chain grid transversal. Normal-series composition, rather
than a false subnormality assertion for the stabilizer, supplies the step. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

inductive SolubleCosetShape where
  | unit
  | step (upper : SolubleCosetShape) (p r : ℕ)

def SolubleCosetShape.Carrier : SolubleCosetShape → Type
  | .unit => Unit
  | .step s p r => s.Carrier×PrimeCosetGrid p r

def SolubleCosetShape.LT : (s : SolubleCosetShape) → s.Carrier → s.Carrier → Prop
  | .unit => fun _ _ => False
  | .step s p r => normalQuotientGridLT s.LT (primeCosetGridLT p r)

def SolubleCosetShape.Comparable : (s : SolubleCosetShape) → s.Carrier → s.Carrier → Prop
  | .unit => fun _ _ => True
  | .step s p r => normalQuotientGridComparable s.Comparable (primeCosetGridComparable p r)

def SolubleCosetShape.Primes : SolubleCosetShape → Prop
  | .unit => True
  | .step s p _ => s.Primes ∧ p.Prime

instance solubleCosetShapeFintype (s : SolubleCosetShape) : Fintype s.Carrier := by
  induction s with
  | unit => exact inferInstanceAs (Fintype Unit)
  | step s p r ih =>
    letI := ih
    exact inferInstanceAs (Fintype (s.Carrier×PrimeCosetGrid p r))

structure SolubleOrderedCosetChart {G : Type} [Group G] (H : Subgroup G) where
  shape : SolubleCosetShape
  primes : shape.Primes
  data : OrderedCosetData H ⊤ shape.Carrier shape.LT shape.Comparable

/-- An actual ordered transversal for every subgroup of the original
finite soluble group; its coordinate chains have prime lengths. -/
theorem soluble_ordered_coset_chart
    (G : Type) [Group G] [Finite G] [IsSolvable G] (H : Subgroup G) :
    Nonempty (SolubleOrderedCosetChart H) := by
  suffices hall : ∀ n : ℕ, ∀ (A : Type) [Group A] [Finite A] [IsSolvable A],
      Nat.card A=n → ∀ H : Subgroup A, Nonempty (SolubleOrderedCosetChart H) by
    exact hall (Nat.card G) G rfl H
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro A _ _ _ hcard H
    by_cases hH : H=⊤
    · subst H
      exact ⟨{ shape := .unit, primes := trivial, data := OrderedCosetData.base ⊤ }⟩
    have htop : (⊤ : Subgroup A)≠⊥ := by
      intro ht
      apply hH
      apply top_unique
      rw [ht]
      exact bot_le
    let good : Subgroup A → Prop := fun N => N.Normal ∧ N≠⊥
    obtain ⟨N,_hNtop,hmin⟩ := Finite.exists_le_minimal (p := good) (a := (⊤ : Subgroup A))
      (show good ⊤ from ⟨inferInstance,htop⟩)
    have hN : IsMinimalNormalSubgroup N := by
      refine ⟨hmin.1.1,hmin.1.2,?_⟩
      intro K hK hKne hKN
      exact hmin.eq_of_le ⟨hK,hKne⟩ hKN
    letI : N.Normal := hN.1
    have hcomm := minimalNormal_isMulCommutative_of_isSolvable N hN
    obtain ⟨C⟩ := elementaryMinimalNormalChart_nonempty N hN.2.1 hcomm (by
      intro K hK hKN
      by_cases hb : K=⊥
      · exact Or.inl hb
      · exact Or.inr (hN.2.2 K hK hb hKN))
    letI : Fact C.p.Prime := ⟨C.p_prime⟩
    have hpN : IsPGroup C.p N := IsPGroup.of_card (n := Module.finrank (ZMod C.p) C.V) (by
      calc
        Nat.card N=Nat.card (Multiplicative C.V) := Nat.card_congr C.equiv.toEquiv
        _ = Nat.card C.V := Nat.card_congr Multiplicative.toAdd
        _ = C.p^Module.finrank (ZMod C.p) C.V := by
          rw [Module.natCard_eq_pow_finrank (K := ZMod C.p),Nat.card_zmod])
    let Q := A⧸N
    let q : A →* Q := QuotientGroup.mk' N
    let K := H⊔N
    have hquot : Nat.card Q<n := by
      rw [←hcard,N.card_eq_card_quotient_mul_card_subgroup]
      exact lt_mul_of_one_lt_right Nat.card_pos (N.one_lt_card_iff_ne_bot.mpr hN.2.1)
    obtain ⟨E⟩ := ih (Nat.card Q) hquot Q rfl (K.map q)
    obtain ⟨r,D,hD⟩ := normalPGroup_orbit_orderedTransversal H N hpN
    obtain ⟨F⟩ := orderedTransversal_of_normalQuotient q (QuotientGroup.mk'_surjective N)
      H K (by rw [QuotientGroup.ker_mk']; exact le_sup_right)
      E.shape.LT E.shape.Comparable (primeCosetGridLT C.p r) (primeCosetGridComparable C.p r)
      D (fun a => (QuotientGroup.eq_one_iff (D.repr a)).mpr (hD a)) E.data
    exact ⟨{ shape := .step E.shape C.p r, primes := ⟨E.primes,C.p_prime⟩, data := F }⟩

end SymmetricSubgroupAsymptotics
