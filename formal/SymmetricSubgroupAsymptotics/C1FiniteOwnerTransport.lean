import SymmetricSubgroupAsymptotics.C1FiniteOwnerWitness
import SymmetricSubgroupAsymptotics.C1TernaryPrimeBaseOwner
import SymmetricSubgroupAsymptotics.C1BinaryNineTopOwner

/-!
# Transport of the bounded c=1 owners

The finite certificates construct owner witnesses on executable row groups.
Coverage, however, recognizes an arbitrary original faithful permutation
group only up to an actual group equivalence.  This file proves that the
intrinsic owner structures transport across that equivalence.  In particular,
the cyclic binary-module condition retains the same distinguished vector and
the same conjugate words, while the ternary prime-base condition transports
the actual top kernel and its equivariant coordinates.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

open TernaryA4InvariantSubmodules

variable {G H : Type*} [Group G] [Group H]

namespace C1OddIndexTwoOwnerWitness

/-- A normal ternary subgroup of index two remains such under an actual
ambient group equivalence. -/
def map (W : C1OddIndexTwoOwnerWitness G) (e : G ≃* H) :
    C1OddIndexTwoOwnerWitness H where
  ternary := W.ternary.map e.toMonoidHom
  normal := W.normal.map e.toMonoidHom e.surjective
  ternaryPGroup := W.ternaryPGroup.of_equiv (e.subgroupMap W.ternary)
  index_two := (Subgroup.index_map_equiv W.ternary e).trans W.index_two

end C1OddIndexTwoOwnerWitness

namespace C1TernaryPrimeBaseOwnerWitness

variable (W : C1TernaryPrimeBaseOwnerWitness G) (e : G ≃* H)

/-- The transported natural-A4 top.  Its kernel is identified below with the
literal original kernel, rather than replaced by an abstract isomorphic
ternary group. -/
private def mappedTop : H →* A4 :=
  W.top.comp e.symm.toMonoidHom

/-- Pull the kernel of the transported top back to the actual original top
kernel. -/
private def mappedKernel : (W.mappedTop e).ker →* W.top.ker where
  toFun k := ⟨e.symm k, by
    change W.top (e.symm k) = 1
    exact k.2⟩
  map_one' := by
    apply Subtype.ext
    exact e.symm.map_one
  map_mul' x y := by
    apply Subtype.ext
    exact e.symm.map_mul x y

private theorem mappedKernel_injective :
    Function.Injective (W.mappedKernel e) := by
  intro x y hxy
  apply Subtype.ext
  apply e.symm.injective
  exact congrArg Subtype.val hxy

private theorem mappedKernel_conj (g : H) (k : (W.mappedTop e).ker) :
    W.mappedKernel e (MulAut.conjNormal g k) =
      MulAut.conjNormal (e.symm g) (W.mappedKernel e k) := by
  apply Subtype.ext
  simp only [MulAut.conjNormal_apply, mappedKernel, MonoidHom.coe_mk,
    OneHom.coe_mk, map_mul, map_inv]

/-- The nonsplit ternary prime-base owner transports across an ambient group
equivalence.  The new coordinate map is the old one on the canonically pulled
back kernel, so injectivity and the full conjugation identity are retained. -/
def map : C1TernaryPrimeBaseOwnerWitness H where
  top := W.mappedTop e
  top_surjective := by
    intro a
    obtain ⟨g, hg⟩ := W.top_surjective a
    refine ⟨e g, ?_⟩
    change W.top (e.symm (e g)) = a
    simpa using hg
  coordinates := W.coordinates.comp (W.mappedKernel e)
  coordinates_injective :=
    W.coordinates_injective.comp (W.mappedKernel_injective e)
  coordinates_conjugation := by
    intro g k
    change
      (W.coordinates (W.mappedKernel e (MulAut.conjNormal g k))).toAdd =
        coordinateAction (W.top (e.symm g)).1
          (W.coordinates (W.mappedKernel e k)).toAdd
    rw [W.mappedKernel_conj e]
    exact W.coordinates_conjugation (e.symm g) (W.mappedKernel e k)

end C1TernaryPrimeBaseOwnerWitness

namespace C1BinaryNineTopOwnerWitness

variable {G₀ H₀ Ω Ξ : Type} [Group G₀] [Group H₀]
    [MulAction G₀ Ω] [MulAction H₀ Ξ]
    (W : C1BinaryNineTopOwnerWitness G₀ Ω) (e : G₀ ≃* H₀)

private abbrev mappedBase : Subgroup H₀ := W.base.map e.toMonoidHom

private instance mappedBase_normal : (W.mappedBase e).Normal :=
  W.base_normal.map e.toMonoidHom e.surjective

private instance mappedBase_finite : Finite (W.mappedBase e) :=
  Finite.of_equiv W.base (e.subgroupMap W.base).toEquiv

/-- The equivalence of whole quotients induced by the ambient group
equivalence.  This retains the literal image of the original binary base. -/
private def mappedQuotientEquiv :
    (G₀ ⧸ W.base) ≃* (H₀ ⧸ W.mappedBase e) :=
  QuotientGroup.congr W.base (W.mappedBase e) e rfl

@[simp] private theorem mappedQuotientEquiv_mk (g : G₀) :
    W.mappedQuotientEquiv e (QuotientGroup.mk' W.base g) =
      QuotientGroup.mk' (W.mappedBase e) (e g) := rfl

@[simp] private theorem mappedQuotientEquiv_symm_mk (h : H₀) :
    (W.mappedQuotientEquiv e).symm
        (QuotientGroup.mk' (W.mappedBase e) h) =
      QuotientGroup.mk' W.base (e.symm h) := rfl

variable (r : Ω ≃ Ξ)
    (hr : ∀ (g : G₀) (x : Ω), r (g • x) = e g • r x)

/-- Conjugating the original action permutation by the point equivalence is
the transported action permutation. -/
private theorem permCongr_toPerm
    (hr : ∀ (g : G₀) (x : Ω), r (g • x) = e g • r x) (g : G₀) :
    r.permCongr (MulAction.toPermHom G₀ Ω g) =
      MulAction.toPermHom H₀ Ξ (e g) := by
  apply Equiv.ext
  intro x
  change r (g • r.symm x) = e g • x
  simpa only [r.apply_symm_apply] using hr g (r.symm x)

/-- The binary-base/nine-top owner transports simultaneously across an
ambient group equivalence and an equivariant equivalence of point actions.
The base is its literal image, the whole quotient action is conjugated through
the induced quotient equivalence, and all nine ambient translations are
conjugated through the point equivalence. -/
def map : C1BinaryNineTopOwnerWitness H₀ Ξ where
  base := W.mappedBase e
  base_normal := W.mappedBase_normal e
  base_finite := W.mappedBase_finite e
  base_exponent_two := by
    intro x
    let x' := (e.subgroupMap W.base).symm x
    have hx := W.base_exponent_two x'
    simpa only [map_pow, map_one, x', MulEquiv.apply_symm_apply] using
      congrArg (e.subgroupMap W.base) hx
  base_card_le := by
    calc
      Nat.card (W.mappedBase e) = Nat.card W.base :=
        (Nat.card_congr (e.subgroupMap W.base).toEquiv).symm
      _ ≤ 64 := W.base_card_le
  quotient_three_group :=
    W.quotient_three_group.of_equiv (W.mappedQuotientEquiv e)
  Label := W.Label
  label_card := W.label_card
  translation s := r.permCongr (W.translation s)
  translation_injective :=
    r.permCongr.injective.comp W.translation_injective
  action := W.action.comp (W.mappedQuotientEquiv e).symm.toMonoidHom
  action_injective :=
    W.action_injective.comp (W.mappedQuotientEquiv e).symm.injective
  action_transitive := by
    intro s t
    obtain ⟨q, hq⟩ := W.action_transitive s t
    exact ⟨W.mappedQuotientEquiv e q, by simpa using hq⟩
  conjugation := by
    intro h s
    have hc := congrArg r.permCongr (W.conjugation (e.symm h) s)
    change
      r.permCongr
          (W.translation
            (W.action
              ((W.mappedQuotientEquiv e).symm
                (QuotientGroup.mk' (W.mappedBase e) h)) s)) =
        MulAction.toPermHom H₀ Ξ h * r.permCongr (W.translation s) *
          (MulAction.toPermHom H₀ Ξ h)⁻¹
    rw [W.mappedQuotientEquiv_symm_mk e]
    calc
      _ = r.permCongr
          (MulAction.toPermHom G₀ Ω (e.symm h) * W.translation s *
            (MulAction.toPermHom G₀ Ω (e.symm h))⁻¹) := hc
      _ = r.permCongr (MulAction.toPermHom G₀ Ω (e.symm h)) *
          r.permCongr (W.translation s) *
            (r.permCongr (MulAction.toPermHom G₀ Ω (e.symm h)))⁻¹ := by
        change r.permCongrHom
            (MulAction.toPermHom G₀ Ω (e.symm h) * W.translation s *
              (MulAction.toPermHom G₀ Ω (e.symm h))⁻¹) =
          r.permCongrHom (MulAction.toPermHom G₀ Ω (e.symm h)) *
            r.permCongrHom (W.translation s) *
              (r.permCongrHom (MulAction.toPermHom G₀ Ω (e.symm h)))⁻¹
        rw [map_mul, map_mul, map_inv]
      _ = _ := by
        rw [permCongr_toPerm e r hr, e.apply_symm_apply]

end C1BinaryNineTopOwnerWitness

namespace C1CyclicBinaryModuleOwnerWitness

variable (W : C1CyclicBinaryModuleOwnerWitness G) (e : G ≃* H)

private abbrev mappedBase : Subgroup H := W.base.map e.toMonoidHom
private abbrev mappedComplement : Subgroup H := W.complement.map e.toMonoidHom

private theorem map_normalConjugate (v : W.base) (g : G) :
    e.subgroupMap W.base (normalConjugate W.base W.base_normal v g) =
      normalConjugate (W.mappedBase e)
        (W.base_normal.map e.toMonoidHom e.surjective)
        (e.subgroupMap W.base v) (e g) := by
  apply Subtype.ext
  simp only [normalConjugate_coe, MulEquiv.coe_subgroupMap_apply, map_mul,
    map_inv]

private theorem map_conjugate_prod (l : List W.complement) :
    ((l.map (e.subgroupMap W.complement)).map (fun c : W.mappedComplement e =>
      normalConjugate (W.mappedBase e)
        (W.base_normal.map e.toMonoidHom e.surjective)
        (e.subgroupMap W.base W.vector) (c : H))).prod =
      e.subgroupMap W.base
        ((l.map fun c : W.complement =>
          normalConjugate W.base W.base_normal W.vector (c : G)).prod) := by
  induction l with
  | nil =>
      change (1 : W.mappedBase e) = e.subgroupMap W.base 1
      exact (e.subgroupMap W.base).map_one.symm
  | cons c l ih =>
      change
        normalConjugate (W.mappedBase e)
            (W.base_normal.map e.toMonoidHom e.surjective)
            (e.subgroupMap W.base W.vector) (e (c : G)) *
              ((l.map (e.subgroupMap W.complement)).map
                (fun d : W.mappedComplement e =>
                  normalConjugate (W.mappedBase e)
                    (W.base_normal.map e.toMonoidHom e.surjective)
                    (e.subgroupMap W.base W.vector) (d : H))).prod =
          e.subgroupMap W.base
            (normalConjugate W.base W.base_normal W.vector (c : G) *
              (l.map fun d : W.complement =>
                normalConjugate W.base W.base_normal W.vector (d : G)).prod)
      rw [← W.map_normalConjugate e W.vector (c : G), ih, map_mul]
      rfl

/-- A cyclic elementary binary base with its actual elementary ternary
complement transports across an ambient equivalence.  The proof explicitly
maps the factorization and every conjugate in the certified cyclic word. -/
def map : C1CyclicBinaryModuleOwnerWitness H where
  base := W.mappedBase e
  complement := W.mappedComplement e
  base_normal := W.base_normal.map e.toMonoidHom e.surjective
  basePGroup := W.basePGroup.of_equiv (e.subgroupMap W.base)
  complementPGroup := W.complementPGroup.of_equiv (e.subgroupMap W.complement)
  base_exponent_two := by
    intro x
    let x' := (e.subgroupMap W.base).symm x
    have hx := W.base_exponent_two x'
    simpa only [map_pow, map_one, x', MulEquiv.apply_symm_apply] using
      congrArg (e.subgroupMap W.base) hx
  complement_exponent_three := by
    intro x
    let x' := (e.subgroupMap W.complement).symm x
    have hx := W.complement_exponent_three x'
    simpa only [map_pow, map_one, x', MulEquiv.apply_symm_apply] using
      congrArg (e.subgroupMap W.complement) hx
  intersection_trivial := by
    intro x hxBase hxComplement
    have hxBase' : e.symm x ∈ W.base :=
      (Subgroup.mem_map_equiv).mp hxBase
    have hxComplement' : e.symm x ∈ W.complement :=
      (Subgroup.mem_map_equiv).mp hxComplement
    have hx := W.intersection_trivial (e.symm x) hxBase' hxComplement'
    calc
      x = e (e.symm x) := (e.apply_symm_apply x).symm
      _ = e 1 := congrArg e hx
      _ = 1 := e.map_one
  factorBase := fun x => e.subgroupMap W.base (W.factorBase (e.symm x))
  factorComplement := fun x =>
    e.subgroupMap W.complement (W.factorComplement (e.symm x))
  factorization := by
    intro x
    change e (W.factorBase (e.symm x) : G) *
        e (W.factorComplement (e.symm x) : G) = x
    rw [← e.map_mul, W.factorization, e.apply_symm_apply]
  vector := e.subgroupMap W.base W.vector
  cyclicWord := fun x =>
    (W.cyclicWord ((e.subgroupMap W.base).symm x)).map
      (e.subgroupMap W.complement)
  cyclic_word_eq := by
    intro x
    let x' := (e.subgroupMap W.base).symm x
    calc
      _ = e.subgroupMap W.base
          (((W.cyclicWord x').map fun c : W.complement =>
            normalConjugate W.base W.base_normal W.vector (c : G)).prod) := by
        simpa only [x'] using W.map_conjugate_prod e (W.cyclicWord x')
      _ = e.subgroupMap W.base x' :=
        congrArg (e.subgroupMap W.base) (W.cyclic_word_eq x')
      _ = x := (e.subgroupMap W.base).apply_symm_apply x

end C1CyclicBinaryModuleOwnerWitness

end SymmetricSubgroupAsymptotics

end
