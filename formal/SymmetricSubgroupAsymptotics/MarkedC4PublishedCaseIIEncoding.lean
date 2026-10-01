import SymmetricSubgroupAsymptotics.BinaryStructuredEpiPolynomial
import SymmetricSubgroupAsymptotics.MarkedC4BoundedWordAssembly

/-!
# Literal Case-II epimorphism encoding

The excessive branch of the RDT bounded-word argument records a residual
object and one epimorphism onto a fixed binary quotient.  This file counts
that literal finite encoding with the unconditional structured epimorphism
theorem.  Thus the exponential Case-II row is a conclusion, rather than a
field of the literature interface.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace MarkedC4

universe u

/-- An actual finite binary group, used for both the fixed excessive quotient
and the residual source extracted by the published construction. -/
structure FiniteBinaryGroup where
  Carrier : Type u
  [group : Group Carrier]
  [finite : Finite Carrier]
  binary : IsPGroup 2 Carrier

attribute [instance] FiniteBinaryGroup.group FiniteBinaryGroup.finite

/-- A literal excessive-factor encoding over all auxiliary mark counts.
Nothing in this structure is an exponential count.  The only numerical
fields bound the two actual source ranks and the finite, unmarked code type.
-/
structure PublishedCaseIIEpiEncoding
    (peel residualCount : ℕ → ℝ) (b d n : ℕ) (A₀ A : ℝ) where
  target : FiniteBinaryGroup
  Code : Type u
  codeFintype : Fintype Code
  Residual : ℕ → Type u
  residualFintype : ∀ r, Fintype (Residual r)
  source : ∀ r, Residual r → FiniteBinaryGroup
  Object : ℕ → Type u
  objectFintype : ∀ r, Fintype (Object r)
  encode : ∀ r, Object r →
    Code × (Σ L : Residual r,
      {f : (source r L).Carrier →* target.Carrier // Function.Surjective f})
  encode_injective : ∀ r, Function.Injective (encode r)
  peel_identity : ∀ r, peel r = (Nat.card (Object r) : ℝ)
  residual_identity : ∀ r, residualCount r = (Nat.card (Residual r) : ℝ)
  character_rank : ∀ r L, binaryCharacterRank (source r L).Carrier ≤ d + r
  derived_rank : ∀ r L, primeDerivedNormalRank 2 (source r L).Carrier ≤ n
  d_le_degree : d ≤ b
  A₀_nonneg : 0 ≤ A₀
  code_bound : (Fintype.card Code : ℝ) ≤ (((b : ℝ) + 2) ^ A₀)
  A_large : A₀ + 2 * binaryStructuredEpiConstant target.Carrier ≤ A

namespace PublishedCaseIIEpiEncoding

variable {peel residualCount : ℕ → ℝ} {b d n : ℕ} {A₀ A : ℝ}

/-- The literal encoding gives the Case-II epimorphism row.  The target
centre and derived slopes are read from the actual quotient. -/
theorem bound
    (D : PublishedCaseIIEpiEncoding peel residualCount b d n A₀ A)
    (r : ℕ) :
    peel r ≤
      (2 : ℝ) ^
        (Nat.log 2 (Nat.card (Subgroup.center D.target.Carrier)) * (d + r) +
          Nat.log 2 (Nat.card (commutator D.target.Carrier)) * n : ℕ) *
        (((b : ℝ) + r + 2) ^ A) * residualCount r := by
  let C : ℕ := binaryStructuredEpiConstant D.target.Carrier
  let z : ℕ := Nat.log 2 (Nat.card (Subgroup.center D.target.Carrier))
  let g : ℕ := Nat.log 2 (Nat.card (commutator D.target.Carrier))
  let x : ℝ := (b : ℝ) + r + 2
  letI : Fintype D.Code := D.codeFintype
  letI : Fintype (D.Residual r) := D.residualFintype r
  letI : Fintype (D.Object r) := D.objectFintype r
  let Epi (L : D.Residual r) :=
    {f : (D.source r L).Carrier →* D.target.Carrier // Function.Surjective f}
  letI (L : D.Residual r) : Finite (Epi L) := by
    dsimp only [Epi]
    infer_instance
  letI : Finite (Σ L : D.Residual r, Epi L) := inferInstance
  letI : Finite (D.Code × (Σ L : D.Residual r, Epi L)) := inferInstance
  have hinj : Nat.card (D.Object r) ≤
      Nat.card (D.Code × (Σ L : D.Residual r, Epi L)) :=
    Nat.card_le_card_of_injective (D.encode r) (D.encode_injective r)
  have hx2 : 2 ≤ x := by
    dsimp only [x]
    have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    linarith
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx2
  have hdrx : ((d + r + 2 : ℕ) : ℝ) ≤ x := by
    dsimp only [x]
    exact_mod_cast Nat.add_le_add_right (Nat.add_le_add_right D.d_le_degree r) 2
  have hEpiNat (L : D.Residual r) :
      Nat.card (Epi L) ≤
        C * (d + r + 2) ^ C * 2 ^ (z * (d + r) + g * n) := by
    have hraw := binaryStructured_epimorphism_card_le_polynomial
      (D.source r L).binary D.target.binary
    dsimp only [Epi, C, z, g]
    have hchar : binaryCharacterRank (D.source r L).Carrier + 2 ≤ d + r + 2 :=
      Nat.add_le_add_right (D.character_rank r L) 2
    have hpolyNat :
        (binaryCharacterRank (D.source r L).Carrier + 2) ^
            binaryStructuredEpiConstant D.target.Carrier ≤
          (d + r + 2) ^ binaryStructuredEpiConstant D.target.Carrier :=
      Nat.pow_le_pow_left hchar _
    have hexpNat :
        Nat.log 2 (Nat.card (Subgroup.center D.target.Carrier)) *
              binaryCharacterRank (D.source r L).Carrier +
            Nat.log 2 (Nat.card (commutator D.target.Carrier)) *
              primeDerivedNormalRank 2 (D.source r L).Carrier ≤
          Nat.log 2 (Nat.card (Subgroup.center D.target.Carrier)) * (d + r) +
            Nat.log 2 (Nat.card (commutator D.target.Carrier)) * n :=
      Nat.add_le_add
        (Nat.mul_le_mul_left _ (D.character_rank r L))
        (Nat.mul_le_mul_left _ (D.derived_rank r L))
    exact hraw.trans (Nat.mul_le_mul
      (Nat.mul_le_mul_left _ hpolyNat)
      (Nat.pow_le_pow_right (by norm_num) hexpNat))
  have hEpi (L : D.Residual r) :
      (Nat.card (Epi L) : ℝ) ≤
        (x ^ (2 * C : ℕ)) *
          (2 : ℝ) ^ (z * (d + r) + g * n : ℕ) := by
    have hcast :
        (Nat.card (Epi L) : ℝ) ≤
          C * ((d + r + 2 : ℕ) : ℝ) ^ C *
            (2 : ℝ) ^ (z * (d + r) + g * n : ℕ) := by
      exact_mod_cast hEpiNat L
    have hC : (C : ℝ) ≤ x ^ C := by
      have hCpow : C ≤ 2 ^ C := by
        induction C with
        | zero => simp
        | succ C ih =>
            rw [pow_succ]
            have hpos : 1 ≤ 2 ^ C := Nat.one_le_two_pow
            omega
      calc
        (C : ℝ) ≤ (2 ^ C : ℕ) := by exact_mod_cast hCpow
        _ = (2 : ℝ) ^ C := by norm_num
        _ ≤ x ^ C := pow_le_pow_left₀ (by norm_num) hx2 C
    have hdPow : (((d + r + 2 : ℕ) : ℝ) ^ C) ≤ x ^ C :=
      pow_le_pow_left₀ (by positivity) hdrx C
    calc
      (Nat.card (Epi L) : ℝ) ≤
          C * ((d + r + 2 : ℕ) : ℝ) ^ C *
            (2 : ℝ) ^ (z * (d + r) + g * n : ℕ) := hcast
      _ ≤ (x ^ C * x ^ C) *
            (2 : ℝ) ^ (z * (d + r) + g * n : ℕ) := by
        gcongr
      _ = (x ^ (2 * C : ℕ)) *
            (2 : ℝ) ^ (z * (d + r) + g * n : ℕ) := by
        rw [← pow_add]
        congr 2
        omega
  have hsum :
      (Nat.card (Σ L : D.Residual r, Epi L) : ℝ) ≤
        (Nat.card (D.Residual r) : ℝ) *
          ((x ^ (2 * C : ℕ)) *
            (2 : ℝ) ^ (z * (d + r) + g * n : ℕ)) := by
    rw [Nat.card_sigma]
    push_cast
    calc
      (∑ L : D.Residual r, (Nat.card (Epi L) : ℝ)) ≤
          ∑ _L : D.Residual r,
            ((x ^ (2 * C : ℕ)) *
              (2 : ℝ) ^ (z * (d + r) + g * n : ℕ)) :=
        Finset.sum_le_sum (fun L _ ↦ hEpi L)
      _ = (Nat.card (D.Residual r) : ℝ) *
          ((x ^ (2 * C : ℕ)) *
            (2 : ℝ) ^ (z * (d + r) + g * n : ℕ)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Fintype.card_eq_nat_card]
  have hobjects :
      (Nat.card (D.Object r) : ℝ) ≤
        (Fintype.card D.Code : ℝ) * (Nat.card (D.Residual r) : ℝ) *
          ((x ^ (2 * C : ℕ)) *
            (2 : ℝ) ^ (z * (d + r) + g * n : ℕ)) := by
    have hinjR : (Nat.card (D.Object r) : ℝ) ≤
        (Fintype.card D.Code : ℝ) *
          (Nat.card (Σ L : D.Residual r, Epi L) : ℝ) := by
      calc
        (Nat.card (D.Object r) : ℝ) ≤
            (Nat.card (D.Code × (Σ L : D.Residual r, Epi L)) : ℕ) := by
          exact_mod_cast hinj
        _ = (Fintype.card D.Code : ℝ) *
            (Nat.card (Σ L : D.Residual r, Epi L) : ℝ) := by
          rw [Nat.card_prod, Nat.card_eq_fintype_card]
          push_cast
          rfl
    calc
      (Nat.card (D.Object r) : ℝ) ≤
          (Fintype.card D.Code : ℝ) *
            (Nat.card (Σ L : D.Residual r, Epi L) : ℝ) := hinjR
      _ ≤ (Fintype.card D.Code : ℝ) *
          ((Nat.card (D.Residual r) : ℝ) *
            ((x ^ (2 * C : ℕ)) *
              (2 : ℝ) ^ (z * (d + r) + g * n : ℕ))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by ring
  have hbase : (b : ℝ) + 2 ≤ x := by
    dsimp only [x]
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    linarith
  have hcode : (Fintype.card D.Code : ℝ) ≤ x ^ A₀ :=
    D.code_bound.trans (Real.rpow_le_rpow (by positivity) hbase D.A₀_nonneg)
  have hdegree : (A₀ + (2 * C : ℕ) : ℝ) ≤ A := by
    push_cast
    exact D.A_large
  have hpoly : (x ^ A₀) * x ^ (2 * C : ℕ) ≤ x ^ A := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_add hxpos]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) hdegree
  rw [D.peel_identity, D.residual_identity]
  dsimp only [C, z, g] at hobjects ⊢
  calc
    (Nat.card (D.Object r) : ℝ) ≤
        (Fintype.card D.Code : ℝ) * (Nat.card (D.Residual r) : ℝ) *
          ((x ^ (2 * binaryStructuredEpiConstant D.target.Carrier : ℕ)) *
            (2 : ℝ) ^
              (Nat.log 2 (Nat.card (Subgroup.center D.target.Carrier)) * (d + r) +
                Nat.log 2 (Nat.card (commutator D.target.Carrier)) * n : ℕ)) := hobjects
    _ ≤ (x ^ A₀) * (Nat.card (D.Residual r) : ℝ) *
          ((x ^ (2 * binaryStructuredEpiConstant D.target.Carrier : ℕ)) *
            (2 : ℝ) ^
              (Nat.log 2 (Nat.card (Subgroup.center D.target.Carrier)) * (d + r) +
                Nat.log 2 (Nat.card (commutator D.target.Carrier)) * n : ℕ)) := by
      gcongr
    _ ≤ (2 : ℝ) ^
          (Nat.log 2 (Nat.card (Subgroup.center D.target.Carrier)) * (d + r) +
            Nat.log 2 (Nat.card (commutator D.target.Carrier)) * n : ℕ) *
          (x ^ A) * (Nat.card (D.Residual r) : ℝ) := by
      have hp := hpoly
      dsimp only [C] at hp
      calc
        (x ^ A₀) * (Nat.card (D.Residual r) : ℝ) *
            ((x ^ (2 * binaryStructuredEpiConstant D.target.Carrier : ℕ)) *
              (2 : ℝ) ^
                (Nat.log 2 (Nat.card (Subgroup.center D.target.Carrier)) * (d + r) +
                  Nat.log 2 (Nat.card (commutator D.target.Carrier)) * n : ℕ)) =
            ((x ^ A₀) *
              x ^ (2 * binaryStructuredEpiConstant D.target.Carrier : ℕ)) *
              (2 : ℝ) ^
                (Nat.log 2 (Nat.card (Subgroup.center D.target.Carrier)) * (d + r) +
                  Nat.log 2 (Nat.card (commutator D.target.Carrier)) * n : ℕ) *
              (Nat.card (D.Residual r) : ℝ) := by ring
        _ ≤ (x ^ A) *
              (2 : ℝ) ^
                (Nat.log 2 (Nat.card (Subgroup.center D.target.Carrier)) * (d + r) +
                  Nat.log 2 (Nat.card (commutator D.target.Carrier)) * n : ℕ) *
              (Nat.card (D.Residual r) : ℝ) := by
          gcongr
        _ = _ := by ring
    _ = _ := by rfl

end PublishedCaseIIEpiEncoding

end MarkedC4
end SymmetricSubgroupAsymptotics

end
