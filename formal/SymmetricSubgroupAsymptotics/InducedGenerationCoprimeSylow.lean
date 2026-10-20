import SymmetricSubgroupAsymptotics.InducedDoubleCosetIndices
import SymmetricSubgroupAsymptotics.RepresentationGeneratorRestrictionMaschke
import SymmetricSubgroupAsymptotics.FiniteModulePaddedGenerators
import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.Algebra.Field.ZMod

/-! Literal double-coset generators for the original induced representation.
When the restricted acting subgroup has invertible order, Maschke makes
this same bound uniform on all actual subrepresentations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators MonoidAlgebra TensorProduct
namespace SymmetricSubgroupAsymptotics

variable {k G V : Type} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]

omit [FiniteDimensional k V] in
theorem induced_mk_left_twist (H : Subgroup G) (rho : Representation k H V)
    (h : H) (g : G) (v : V) :
    Representation.IndV.mk H.subtype rho ((h : G)*g) v =
      Representation.IndV.mk H.subtype rho g (rho h⁻¹ v) := by
  change Representation.Coinvariants.mk _
      (Finsupp.single ((h : G)*g) 1 ⊗ₜ[k] v) =
    Representation.Coinvariants.mk _ (Finsupp.single g 1 ⊗ₜ[k] rho h⁻¹ v)
  simpa using (Representation.Coinvariants.mk_inv_tmul
    ((Representation.leftRegular k G).comp H.subtype) rho
    (Finsupp.single g 1) v h⁻¹)

theorem induced_restriction_generated_doubleCosets
    (H P : Subgroup G) (rho : Representation k H V)
    [Fintype (DoubleCoset.Quotient (H : Set G) (P : Set G))] :
    RepresentationGeneratedBy ((Representation.ind H.subtype rho).comp P.subtype)
      (Fintype.card (DoubleCoset.Quotient (H : Set G) (P : Set G))*Module.finrank k V) := by
  let Q := DoubleCoset.Quotient (H : Set G) (P : Set G)
  let d := Module.finrank k V
  let basis := Module.finBasis k V
  let R : Representation k P (Representation.IndV H.subtype rho) :=
    (Representation.ind H.subtype rho).comp P.subtype
  let generators : Q×Fin d → R.asModule := fun z =>
    R.asModuleEquiv.symm (Representation.IndV.mk H.subtype rho z.1.out (basis z.2))
  let S : Finset R.asModule := Finset.univ.image generators
  let A : Submodule k[P] R.asModule := Submodule.span k[P] (S : Set R.asModule)
  let W : Subrepresentation R := Subrepresentation.ofSubmodule' A
  have hlocal (q : Q) (v : V) : Representation.IndV.mk H.subtype rho q.out v∈W.toSubmodule := by
    have hb : Submodule.span k (Set.range basis)≤
        W.toSubmodule.comap (Representation.IndV.mk H.subtype rho q.out) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j,rfl⟩
      change generators (q,j)∈A
      exact Submodule.subset_span (Finset.mem_image.mpr ⟨(q,j),Finset.mem_univ _,rfl⟩)
    apply hb
    rw [basis.span_eq]
    trivial
  have hall (g : G) (v : V) : Representation.IndV.mk H.subtype rho g v∈W.toSubmodule := by
    let q : Q := DoubleCoset.mk H P g
    obtain ⟨h,hh,t,ht,hg⟩ := (DoubleCoset.eq H P q.out g).mp
      (DoubleCoset.out_eq' H P q)
    rw [hg,mul_assoc,induced_mk_left_twist H rho ⟨h,hh⟩]
    have hm := W.apply_mem_toSubmodule (⟨t,ht⟩ : P)⁻¹ (hlocal q (rho (⟨h,hh⟩ : H)⁻¹ v))
    change Representation.ind H.subtype rho t⁻¹
      (Representation.IndV.mk H.subtype rho q.out (rho (⟨h,hh⟩ : H)⁻¹ v))∈W.toSubmodule at hm
    rw [Representation.ind_mk,inv_inv] at hm
    exact hm
  have hzero : W.toSubmodule.mkQ=0 := by
    apply Representation.IndV.hom_ext
    intro g
    ext v
    exact (Submodule.Quotient.mk_eq_zero W.toSubmodule).mpr (hall g v)
  have hA : A=⊤ := by
    apply top_unique
    intro x _
    have hx : R.asModuleEquiv x∈W.toSubmodule := by
      apply (Submodule.Quotient.mk_eq_zero W.toSubmodule).mp
      exact DFunLike.congr_fun hzero (R.asModuleEquiv x)
    exact hx
  exact ModuleGeneratedBy.of_finset_card_le S hA _ (by
    calc
      S.card≤(Finset.univ : Finset (Q×Fin d)).card := Finset.card_image_le
      _ = Fintype.card Q*d := by simp
      _ = _ := rfl)

theorem induced_coprime_subgroup_uniform
    (H P : Subgroup G) [Finite P] [NeZero (Nat.card P : k)]
    (rho : Representation k H V)
    [Fintype (DoubleCoset.Quotient (H : Set G) (P : Set G))] :
    UniformSubrepresentationGeneratorBound (Representation.ind H.subtype rho)
      (Fintype.card (DoubleCoset.Quotient (H : Set G) (P : Set G))*Module.finrank k V) :=
  UniformSubrepresentationGeneratorBound.of_comp _ P.subtype
    (RepresentationGeneratedBy.uniform_of_invertible_order _
      (induced_restriction_generated_doubleCosets H P rho))

/-- Literal double-coset count pays any displayed prime-power divisor of
the original index. Every local orbit keeps its own actual stabilizer. -/
theorem inducedSylow_doubleCoset_count [Finite G]
    (q : ℕ) [Fact q.Prime] (H : Subgroup G) (P : Sylow q G)
    [Fintype (DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G))]
    (e : ℕ) (hdiv : q^e∣H.index) :
    Fintype.card (DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G))*q^e≤H.index := by
  obtain ⟨j,_,hval,hsum⟩ := inducedMackeySylow_indices H q P
  have he : e≤H.index.factorization q := by
    have hh := (Nat.factorization_le_iff_dvd
      (pow_ne_zero e (Fact.out : q.Prime).ne_zero) H.index_ne_zero_of_finite).mpr hdiv q
    simpa only [Nat.factorization_pow_self (Fact.out : q.Prime)] using hh
  calc
    _ = ∑ _a : DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G),q^e := by simp
    _ ≤ ∑ a,q^j a := Finset.sum_le_sum (fun a _ =>
      Nat.pow_le_pow_right (Fact.out : q.Prime).pos (he.trans (hval a)))
    _ = H.index := hsum

theorem induced_coprime_sylow_uniform_with_price
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hqp : q≠p)
    {G V : Type} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V]
    (H : Subgroup G) (P : Sylow q G) (rho : Representation (ZMod p) H V)
    [Fintype (DoubleCoset.Quotient (H : Set G) ((P : Subgroup G) : Set G))]
    (e : ℕ) (hdiv : q^e∣H.index) :
    ∃ B : ℕ, UniformSubrepresentationGeneratorBound (Representation.ind H.subtype rho) B ∧
      B*q^e≤Module.finrank (ZMod p) V*H.index := by
  have hn : (Nat.card P : ZMod p)≠0 := by
    intro hz
    have hd : p∣Nat.card P := (ZMod.natCast_eq_zero_iff _ _).mp hz
    obtain ⟨r,hr⟩ := P.isPGroup'.exists_card_eq
    rw [hr] at hd
    have hpq := (Fact.out : p.Prime).dvd_of_dvd_pow hd
    rcases (Nat.dvd_prime (Fact.out : q.Prime)).mp hpq with hp1 | hpq
    · exact (Fact.out : p.Prime).ne_one hp1
    · exact hqp hpq.symm
  letI : NeZero (Nat.card P : ZMod p) := ⟨hn⟩
  refine ⟨_,induced_coprime_subgroup_uniform H (P : Subgroup G) rho,?_⟩
  have hc := inducedSylow_doubleCoset_count q H P e hdiv
  simpa only [mul_assoc,mul_left_comm,mul_comm] using
    Nat.mul_le_mul_left (Module.finrank (ZMod p) V) hc

end SymmetricSubgroupAsymptotics
