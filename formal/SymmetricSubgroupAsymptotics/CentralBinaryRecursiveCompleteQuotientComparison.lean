import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignCentralSeries
import SymmetricSubgroupAsymptotics.BinaryStructuredPolynomialBound

/-!
# Recursive complete comparison through a central binary step

The direct central-binary comparison asks the fixed comparator to map onto
both the projective target and its product with `C₂`.  Iterating that
interface is awkward when the projective target is itself a central binary
extension (the cyclic order-four case is the first example).

This file records the recursive form.  It is enough to have complete-weight
bounds for `A` and `A × C₂`; every quotient appearing after descent from
`R` is then controlled by the corresponding quotient of one of those two
groups.  The result keeps the exact finite coefficient, and a uniform
power-of-two estimate is supplied for later numerical assembly.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

attribute [-instance] originalNormalFintype

private abbrev C2 := Multiplicative (ZMod 2)
private abbrev NormalAxis (G : Type*) [Group G] :=
  {N : Subgroup G // N.Normal}

/-- One central-binary axis whose two projective terms have already been
bounded by a common comparator. -/
structure CentralBinaryAxisWeightComparison
    (Q X : Type*) [Group Q] [Finite Q] [Group X] [Finite X] where
  A : Type
  [groupA : Group A]
  [finiteA : Finite A]
  projection : X →* A
  projection_surjective : Function.Surjective projection
  central_kernel : ∀ z ∈ projection.ker, ∀ x : X, z * x = x * z
  kernelCharacter : projection.ker →* C2
  kernelCharacter_injective : Function.Injective kernelCharacter
  baseCoefficient : ℕ
  productCoefficient : ℕ
  base_bound : ∀ {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))),
    (Nat.card (GroupEpimorphism J A) : ℝ) ≤
      (baseCoefficient : ℝ) * completeQuotientWeight (R := Q) J
  product_bound : ∀ {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))),
    (Nat.card (GroupEpimorphism J (A × C2)) : ℝ) ≤
      (productCoefficient : ℝ) * completeQuotientWeight (R := Q) J

attribute [instance]
  CentralBinaryAxisWeightComparison.groupA
  CentralBinaryAxisWeightComparison.finiteA

namespace CentralBinaryAxisWeightComparison

variable {Q X : Type*} [Group Q] [Finite Q] [Group X] [Finite X]
  (D : CentralBinaryAxisWeightComparison Q X)

/-- Homomorphisms into the central kernel inject into binary characters. -/
theorem kernel_hom_card_le
    {J : Type*} [Group J] [Finite J] :
    Nat.card (J →* D.projection.ker) ≤ Nat.card (J →* C2) := by
  letI : Finite (J →* D.projection.ker) :=
    Finite.of_injective
      (fun f : J →* D.projection.ker ↦ (f : J → D.projection.ker))
      DFunLike.coe_injective
  letI : Finite (J →* C2) :=
    Finite.of_injective (fun f : J →* C2 ↦ (f : J → C2))
      DFunLike.coe_injective
  exact Nat.card_le_card_of_injective
    (fun f : J →* D.projection.ker ↦ D.kernelCharacter.comp f)
    (fun f g h ↦ MonoidHom.ext fun x ↦ D.kernelCharacter_injective
      (DFunLike.congr_fun h x))

/-- Recursive one-axis estimate.  The coefficient records the already
proved bounds for the projective quotient and its binary product. -/
theorem epi_card_le {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J X) : ℝ) ≤
      ((D.productCoefficient +
          D.baseCoefficient * Nat.card (D.A →* C2) : ℕ) : ℝ) *
        completeQuotientWeight (R := Q) J := by
  have hlift := epi_card_le_centralLift (J := J) D.projection
    D.projection_surjective D.central_kernel
  have hker := D.kernel_hom_card_le (J := J)
  have htwist := epi_mul_hom_two_le_general (J := J) (A := D.A)
  have hliftReal :
      (Nat.card (GroupEpimorphism J X) : ℝ) ≤
        (Nat.card (GroupEpimorphism J D.A) : ℝ) *
          Nat.card (J →* D.projection.ker) := by
    exact_mod_cast hlift
  have hkerReal :
      (Nat.card (J →* D.projection.ker) : ℝ) ≤
        Nat.card (J →* C2) := by
    exact_mod_cast hker
  have htwistReal :
      (Nat.card (GroupEpimorphism J D.A) : ℝ) *
          Nat.card (J →* C2) ≤
        Nat.card (GroupEpimorphism J (D.A × C2)) +
          (Nat.card (GroupEpimorphism J D.A) : ℝ) *
            Nat.card (D.A →* C2) := by
    exact_mod_cast htwist
  calc
    (Nat.card (GroupEpimorphism J X) : ℝ) ≤
        (Nat.card (GroupEpimorphism J D.A) : ℝ) *
          Nat.card (J →* D.projection.ker) := hliftReal
    _ ≤ (Nat.card (GroupEpimorphism J D.A) : ℝ) *
          Nat.card (J →* C2) :=
      mul_le_mul_of_nonneg_left hkerReal (Nat.cast_nonneg _)
    _ ≤ Nat.card (GroupEpimorphism J (D.A × C2)) +
          (Nat.card (GroupEpimorphism J D.A) : ℝ) *
            Nat.card (D.A →* C2) := htwistReal
    _ ≤ D.productCoefficient * completeQuotientWeight (R := Q) J +
          (D.baseCoefficient * completeQuotientWeight (R := Q) J) *
            Nat.card (D.A →* C2) := by
      exact add_le_add (D.product_bound J)
        (mul_le_mul_of_nonneg_right (D.base_bound J) (Nat.cast_nonneg _))
    _ = ((D.productCoefficient +
          D.baseCoefficient * Nat.card (D.A →* C2) : ℕ) : ℝ) *
        completeQuotientWeight (R := Q) J := by
      push_cast
      ring

end CentralBinaryAxisWeightComparison

/-- A central binary extension together with already proved complete bounds
for its projective quotient and the quotient times `C₂`. -/
structure CentralBinaryRecursiveComparison
    (Q R : Type*) (A : Type)
    [Group Q] [Finite Q] [Group R] [Finite R] [Group A] [Finite A] where
  projection : R →* A
  projection_surjective : Function.Surjective projection
  central_kernel : ∀ z ∈ projection.ker, ∀ x : R, z * x = x * z
  kernel_card_le_two : Nat.card projection.ker ≤ 2
  baseCoefficient : ℕ
  productCoefficient : ℕ
  base_complete_bound : ∀ {b : ℕ}
      (J : Subgroup (Equiv.Perm (Fin b))),
    completeQuotientWeight (R := A) J ≤
      (baseCoefficient : ℝ) * completeQuotientWeight (R := Q) J
  product_complete_bound : ∀ {b : ℕ}
      (J : Subgroup (Equiv.Perm (Fin b))),
    completeQuotientWeight (R := A × C2) J ≤
      (productCoefficient : ℝ) * completeQuotientWeight (R := Q) J

namespace CentralBinaryRecursiveComparison

variable {Q R : Type*} {A : Type}
  [Group Q] [Finite Q] [Group R] [Finite R] [Group A] [Finite A]
  (D : CentralBinaryRecursiveComparison Q R A)

/-- The direct quotient-map interface is the coefficient-one base case of
the recursive comparison. -/
noncomputable def ofGlobal
    (G : CentralBinaryGlobalComparison Q R A) :
    CentralBinaryRecursiveComparison Q R A where
  projection := G.projection
  projection_surjective := G.projection_surjective
  central_kernel := G.central_kernel
  kernel_card_le_two := G.kernel_card_le_two
  baseCoefficient := 1
  productCoefficient := 1
  base_complete_bound := by
    intro b J
    simpa only [Nat.cast_one, one_mul] using
      completeQuotientWeight_le_of_surjective
        G.baseQuotient G.baseQuotient_surjective J
  product_complete_bound := by
    intro b J
    simpa only [Nat.cast_one, one_mul] using
      completeQuotientWeight_le_of_surjective
        G.productQuotient G.productQuotient_surjective J

/-- Product with one binary factor preserves the same central kernel.  The
base estimate is the preceding product estimate; only the next binary
product estimate has to be supplied. -/
noncomputable def prodC2
    (nextCoefficient : ℕ)
    (next_complete_bound : ∀ {b : ℕ}
      (J : Subgroup (Equiv.Perm (Fin b))),
      completeQuotientWeight (R := (A × C2) × C2) J ≤
        (nextCoefficient : ℝ) * completeQuotientWeight (R := Q) J) :
    CentralBinaryRecursiveComparison Q (R × C2) (A × C2) := by
  let projectionProduct : R × C2 →* A × C2 :=
    D.projection.prodMap (MonoidHom.id C2)
  let kernelFst : projectionProduct.ker →* D.projection.ker :=
    { toFun := fun z =>
        (⟨z.1.1, by
          have hz := MonoidHom.mem_ker.mp z.2
          exact MonoidHom.mem_ker.mpr (congrArg Prod.fst hz)⟩ :
            D.projection.ker)
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl }
  have hkernelFst : Function.Injective kernelFst := by
    intro x y hxy
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val hxy
    · have hx := MonoidHom.mem_ker.mp x.2
      have hy := MonoidHom.mem_ker.mp y.2
      exact (congrArg Prod.snd hx).trans (congrArg Prod.snd hy).symm
  refine
    { projection := projectionProduct
      projection_surjective :=
        D.projection_surjective.prodMap Function.surjective_id
      central_kernel := ?_
      kernel_card_le_two :=
        (Nat.card_le_card_of_injective kernelFst hkernelFst).trans
          D.kernel_card_le_two
      baseCoefficient := D.productCoefficient
      productCoefficient := nextCoefficient
      base_complete_bound := D.product_complete_bound
      product_complete_bound := next_complete_bound }
  rintro ⟨z, c⟩ hz ⟨x, d⟩
  have hzpair := MonoidHom.mem_ker.mp hz
  have hzR : z ∈ D.projection.ker :=
    MonoidHom.mem_ker.mpr (congrArg Prod.fst hzpair)
  have hc : c = 1 := congrArg Prod.snd hzpair
  apply Prod.ext
  · exact D.central_kernel z hzR x
  · change c * d = d * c
    rw [hc, one_mul, mul_one]

/-- Descent through one literal normal axis.  Its projective target is the
actual quotient of `A` by the image of that axis. -/
noncomputable def quotient
    (M : NormalAxis R) :
    CentralBinaryAxisWeightComparison Q (R ⧸ M.1) := by
  letI : M.1.Normal := M.2
  let image := ProjectiveCentralQuotient.normalImage
    D.projection D.projection_surjective M
  letI : image.1.Normal := image.2
  let projectionM : (R ⧸ M.1) →* (A ⧸ image.1) :=
    ProjectiveCentralQuotient.map
      D.projection D.projection_surjective M
  let kernelEmbedding := binaryEmbeddingOfCardLETwo projectionM.ker
    ((ProjectiveCentralQuotient.card_kernel_le
        D.projection D.projection_surjective M).trans
      D.kernel_card_le_two)
  refine
    { A := A ⧸ image.1
      projection := projectionM
      projection_surjective :=
        ProjectiveCentralQuotient.map_surjective
          D.projection D.projection_surjective M
      central_kernel :=
        ProjectiveCentralQuotient.central_kernel
          D.projection D.projection_surjective M D.central_kernel
      kernelCharacter := kernelEmbedding.1
      kernelCharacter_injective := kernelEmbedding.2
      baseCoefficient := D.baseCoefficient
      productCoefficient := D.productCoefficient
      base_bound := ?_
      product_bound := ?_ }
  · intro b J
    have hepi :
        (Nat.card (GroupEpimorphism J (A ⧸ image.1)) : ℝ) ≤
          completeQuotientWeight (R := A ⧸ image.1) J := by
      let N : NormalAxis (A ⧸ image.1) := ⟨⊥, inferInstance⟩
      exact card_groupEpimorphism_le_completeQuotientWeight J N
        (QuotientGroup.quotientBot (G := A ⧸ image.1)).symm
    exact hepi.trans ((completeQuotientWeight_le_of_surjective
      (QuotientGroup.mk' image.1)
      (QuotientGroup.mk'_surjective image.1) J).trans
        (D.base_complete_bound J))
  · intro b J
    let productMap : A × C2 →* (A ⧸ image.1) × C2 :=
      (QuotientGroup.mk' image.1).prodMap (MonoidHom.id C2)
    have hproductMap : Function.Surjective productMap :=
      (QuotientGroup.mk'_surjective image.1).prodMap
        Function.surjective_id
    have hepi :
        (Nat.card (GroupEpimorphism J ((A ⧸ image.1) × C2)) : ℝ) ≤
          completeQuotientWeight (R := (A ⧸ image.1) × C2) J := by
      let N : NormalAxis ((A ⧸ image.1) × C2) := ⟨⊥, inferInstance⟩
      exact card_groupEpimorphism_le_completeQuotientWeight J N
        (QuotientGroup.quotientBot
          (G := (A ⧸ image.1) × C2)).symm
    exact hepi.trans ((completeQuotientWeight_le_of_surjective
      productMap hproductMap J).trans (D.product_complete_bound J))

/-- Exact recursive coefficient, summed only after all literal normal axes
of `R` have been descended. -/
def coefficient : ℕ :=
  ∑ M : NormalAxis R,
    ((D.quotient M).productCoefficient +
      (D.quotient M).baseCoefficient *
        Nat.card ((D.quotient M).A →* C2))

theorem coefficient_nonneg : (0 : ℝ) ≤ D.coefficient :=
  Nat.cast_nonneg _

/-- Complete all-normal comparison for a recursively controlled central
binary extension. -/
theorem completeQuotientWeight_le {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := R) J ≤
      (D.coefficient : ℝ) * completeQuotientWeight (R := Q) J := by
  unfold completeQuotientWeight completeQuotientCount
  rw [Nat.cast_sum]
  calc
    (∑ M : NormalAxis R,
        (Nat.card (GroupEpimorphism J (R ⧸ M.1)) : ℝ)) ≤
      ∑ M : NormalAxis R,
        (((D.quotient M).productCoefficient +
          (D.quotient M).baseCoefficient *
            Nat.card ((D.quotient M).A →* C2) : ℕ) : ℝ) *
          completeQuotientWeight (R := Q) J := by
      apply Finset.sum_le_sum
      intro M _
      exact (D.quotient M).epi_card_le J
    _ = (∑ M : NormalAxis R,
          (((D.quotient M).productCoefficient +
            (D.quotient M).baseCoefficient *
              Nat.card ((D.quotient M).A →* C2) : ℕ) : ℝ)) *
          completeQuotientWeight (R := Q) J := by
      rw [Finset.sum_mul]
    _ = (D.coefficient : ℝ) *
          completeQuotientWeight (R := Q) J := by
      congr 1
      unfold coefficient
      rw [Nat.cast_sum]

/-- Uniform numerical bound for the recursive coefficient. -/
theorem coefficient_le_two_pow
    (m a c : ℕ)
    (hR : Nat.card R ≤ 2 ^ m)
    (hA : Nat.card A ≤ a)
    (hbase : D.baseCoefficient ≤ 2 ^ c)
    (hproduct : D.productCoefficient ≤ 2 ^ c) :
    D.coefficient ≤ 2 ^ (m * m + c + a + 1) := by
  have hnormal : Nat.card (NormalAxis R) ≤ 2 ^ (m * m) :=
    normalSubgroup_card_le_two_pow_sq m hR
  have hterm : ∀ M : NormalAxis R,
      (D.quotient M).productCoefficient +
          (D.quotient M).baseCoefficient *
            Nat.card ((D.quotient M).A →* C2) ≤
        2 ^ (c + a + 1) := by
    intro M
    letI : M.1.Normal := M.2
    let image := ProjectiveCentralQuotient.normalImage
      D.projection D.projection_surjective M
    have hquotientCard : Nat.card (A ⧸ image.1) ≤ a := by
      exact (Nat.card_le_card_of_surjective
        (QuotientGroup.mk' image.1)
        (QuotientGroup.mk'_surjective image.1)).trans hA
    have hhom : Nat.card ((A ⧸ image.1) →* C2) ≤ 2 ^ a := by
      calc
        Nat.card ((A ⧸ image.1) →* C2) ≤
            Nat.card ((A ⧸ image.1) → C2) :=
          Nat.card_le_card_of_injective
            (fun f : (A ⧸ image.1) →* C2 ↦
              (f : (A ⧸ image.1) → C2))
            DFunLike.coe_injective
        _ = 2 ^ Nat.card (A ⧸ image.1) := by
          rw [Nat.card_fun]
          norm_num [C2]
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hquotientCard
    change D.productCoefficient + D.baseCoefficient *
        Nat.card ((A ⧸ image.1) →* C2) ≤ _
    calc
      D.productCoefficient + D.baseCoefficient *
          Nat.card ((A ⧸ image.1) →* C2) ≤
        2 ^ c + 2 ^ c * 2 ^ a :=
          Nat.add_le_add hproduct (Nat.mul_le_mul hbase hhom)
      _ = 2 ^ c * (1 + 2 ^ a) := by ring
      _ ≤ 2 ^ c * 2 ^ (a + 1) := by
        apply Nat.mul_le_mul_left
        rw [pow_succ]
        have hone : 1 ≤ 2 ^ a := Nat.one_le_two_pow
        omega
      _ = 2 ^ (c + a + 1) := by
        rw [← pow_add]
        congr 1 <;> omega
  unfold coefficient
  calc
    (∑ M : NormalAxis R,
        ((D.quotient M).productCoefficient +
          (D.quotient M).baseCoefficient *
            Nat.card ((D.quotient M).A →* C2))) ≤
      ∑ _M : NormalAxis R, 2 ^ (c + a + 1) := by
        apply Finset.sum_le_sum
        intro M _
        exact hterm M
    _ = Nat.card (NormalAxis R) * 2 ^ (c + a + 1) := by
      simp [Finset.sum_const]
    _ ≤ 2 ^ (m * m) * 2 ^ (c + a + 1) :=
      Nat.mul_le_mul_right _ hnormal
    _ = 2 ^ (m * m + c + a + 1) := by
      rw [← pow_add]
      congr 1 <;> omega

/-- Logarithmic form of the recursive coefficient bound.  Unlike
`coefficient_le_two_pow`, this uses the binary character rank of every
projective quotient, so the parameter `a` bounds the base-two logarithm of
the projective order rather than the order itself.  This is the useful form
for iterating central binary extensions of the ternary section. -/
theorem coefficient_le_two_pow_of_card_le_pow
    (m a c : ℕ)
    (hR : Nat.card R ≤ 2 ^ m)
    (hA : Nat.card A ≤ 2 ^ a)
    (hbase : D.baseCoefficient ≤ 2 ^ c)
    (hproduct : D.productCoefficient ≤ 2 ^ c) :
    D.coefficient ≤ 2 ^ (m * m + c + a + 1) := by
  have hnormal : Nat.card (NormalAxis R) ≤ 2 ^ (m * m) :=
    normalSubgroup_card_le_two_pow_sq m hR
  have hterm : ∀ M : NormalAxis R,
      (D.quotient M).productCoefficient +
          (D.quotient M).baseCoefficient *
            Nat.card ((D.quotient M).A →* C2) ≤
        2 ^ (c + a + 1) := by
    intro M
    letI : M.1.Normal := M.2
    let image := ProjectiveCentralQuotient.normalImage
      D.projection D.projection_surjective M
    have hquotientCard : Nat.card (A ⧸ image.1) ≤ 2 ^ a := by
      exact (Nat.card_le_card_of_surjective
        (QuotientGroup.mk' image.1)
        (QuotientGroup.mk'_surjective image.1)).trans hA
    have hcharacter : binaryCharacterRank (A ⧸ image.1) ≤ a :=
      binaryCharacterRank_le_of_card_le_pow (A ⧸ image.1) a hquotientCard
    have hhom : Nat.card ((A ⧸ image.1) →* C2) ≤ 2 ^ a := by
      have hcard : Nat.card ((A ⧸ image.1) →* C2) =
          2 ^ binaryCharacterRank (A ⧸ image.1) := by
        rw [binaryAbelianizationGroupHom_card]
        simp
      rw [hcard]
      exact Nat.pow_le_pow_right (by norm_num) hcharacter
    change D.productCoefficient + D.baseCoefficient *
        Nat.card ((A ⧸ image.1) →* C2) ≤ _
    calc
      D.productCoefficient + D.baseCoefficient *
          Nat.card ((A ⧸ image.1) →* C2) ≤
        2 ^ c + 2 ^ c * 2 ^ a :=
          Nat.add_le_add hproduct (Nat.mul_le_mul hbase hhom)
      _ = 2 ^ c * (1 + 2 ^ a) := by ring
      _ ≤ 2 ^ c * 2 ^ (a + 1) := by
        apply Nat.mul_le_mul_left
        rw [pow_succ]
        have hone : 1 ≤ 2 ^ a := Nat.one_le_two_pow
        omega
      _ = 2 ^ (c + a + 1) := by
        rw [← pow_add]
        congr 1 <;> omega
  unfold coefficient
  calc
    (∑ M : NormalAxis R,
        ((D.quotient M).productCoefficient +
          (D.quotient M).baseCoefficient *
            Nat.card ((D.quotient M).A →* C2))) ≤
      ∑ _M : NormalAxis R, 2 ^ (c + a + 1) := by
        apply Finset.sum_le_sum
        intro M _
        exact hterm M
    _ = Nat.card (NormalAxis R) * 2 ^ (c + a + 1) := by
      simp [Finset.sum_const]
    _ ≤ 2 ^ (m * m) * 2 ^ (c + a + 1) :=
      Nat.mul_le_mul_right _ hnormal
    _ = 2 ^ (m * m + c + a + 1) := by
      rw [← pow_add]
      congr 1 <;> omega

end CentralBinaryRecursiveComparison
end SymmetricSubgroupAsymptotics

end
