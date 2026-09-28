import SymmetricSubgroupAsymptotics.PermutationBinaryFourSection
import SymmetricSubgroupAsymptotics.PermutationBinaryOrbitSection
import SymmetricSubgroupAsymptotics.SchurPGroupCapacity

/-! The actual augmentation hyperplane at four original points.

A permutation subrepresentation with invariant-form head at least two
must have dimension three. Its one-dimensional quotient is trivial for
the actual binary action, so the subspace is precisely the kernel of
the original coordinate sum. No regular-coordinate chart, list of
submodules, or splitting of a correlated module is used.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics

section HeadDimension

variable {k G V : Type} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V)

theorem representationHead_finrank_le_dimension :
    Module.finrank k (ρ.IntertwiningMap (Representation.trivial k G k))≤
      Module.finrank k V := by
  rw [representationHead_finrank_eq_coinvariants]
  exact LinearMap.finrank_le_finrank_of_surjective
    (Representation.Coinvariants.mk_surjective ρ)

/-- Equality of the full head with the whole dimension forces the
unchanged representation itself to be trivial. -/
theorem representation_trivial_of_head_finrank_eq
    (hd : Module.finrank k (ρ.IntertwiningMap (Representation.trivial k G k))=
      Module.finrank k V) : ∀ g v,ρ g v=v := by
  rw [representationHead_finrank_eq_coinvariants] at hd
  have hi : Function.Injective (Representation.Coinvariants.mk ρ) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd.symm).mpr
      (Representation.Coinvariants.mk_surjective ρ)
  intro g v
  apply hi
  exact Representation.Coinvariants.mk_self_apply ρ g v

end HeadDimension

namespace PermutationAugmentation

variable (k : Type) [Field k] (X : Type) [Finite X]

/-- The sum of the literal original point coordinates. -/
def coordinateSum : (X → k) →ₗ[k] k where
  toFun f := ∑ x,f x
  map_add' f f' := Finset.sum_add_distrib
  map_smul' c f := by simp only [Finset.smul_sum,RingHom.id_apply,Pi.smul_apply]

/-- The original sum-zero hyperplane, without choosing regular labels. -/
def space : Submodule k (X → k) := (coordinateSum k X).ker

variable {k X}

theorem coordinateSum_surjective (x : X) : Function.Surjective (coordinateSum k X) := by
  intro c
  exact ⟨Pi.single x c,by simp [coordinateSum]⟩

theorem space_finrank_add_one (x : X) :
    Module.finrank k (space k X)+1=Nat.card X := by
  have hd := (coordinateSum k X).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (coordinateSum_surjective x),finrank_top,
    Module.finrank_self,Module.finrank_pi,Fintype.card_eq_nat_card] at hd
  change 1+Module.finrank k (space k X)=Nat.card X at hd
  omega

variable {G : Type} [Group G] [MulAction G X]

theorem coordinateSum_permutation (g : G) (f : X → k) :
    coordinateSum k X (permutationFunctionRepresentation k G X g f)=
      coordinateSum k X f :=
  Equiv.sum_comp (MulAction.toPermHom G X g⁻¹) f

theorem coinvariantsKer_le_space :
    Representation.Coinvariants.ker (permutationFunctionRepresentation k G X)≤space k X := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨g,f⟩,rfl⟩
  change coordinateSum k X
    (permutationFunctionRepresentation k G X g f-f)=0
  rw [map_sub,coordinateSum_permutation,sub_self]

variable [MulAction.IsPretransitive G X]

/-- Transitivity identifies the full original coinvariant kernel with
the original sum-zero hyperplane, in every characteristic. -/
theorem coinvariantsKer_eq_space (x : X) :
    Representation.Coinvariants.ker (permutationFunctionRepresentation k G X)=space k X := by
  have hquot := PermutationBinaryFourSection.trivial_quotient_finrank_le_one x
    (Representation.Coinvariants.mk (permutationFunctionRepresentation k G X))
    (Representation.Coinvariants.mk_surjective (permutationFunctionRepresentation k G X))
    (fun g f => Representation.Coinvariants.mk_self_apply _ g f)
  have hsum := (Representation.Coinvariants.ker
    (permutationFunctionRepresentation k G X)).finrank_quotient_add_finrank
  change Module.finrank k (permutationFunctionRepresentation k G X).Coinvariants+
    Module.finrank k (Representation.Coinvariants.ker
      (permutationFunctionRepresentation k G X))=Module.finrank k (X → k) at hsum
  rw [Module.finrank_pi,Fintype.card_eq_nat_card] at hsum
  have hspace := space_finrank_add_one (k := k) x
  apply Submodule.eq_of_le_of_finrank_le (coinvariantsKer_le_space (k := k) (G := G))
  omega

end PermutationAugmentation

namespace PermutationBinaryFourAugmentation

variable {G X : Type} [Group G] [Finite G] [MulAction G X]
    [Finite X] [MulAction.IsPretransitive G X]
    (S : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G X))

/-- A full subspace has the head of the whole original transitive
permutation module. This proof transports the literal coinvariant map. -/
private theorem head_le_one_of_top (x : X) (hS : S.toSubmodule=⊤) :
    Module.finrank (ZMod 2)
      (S.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2)))≤1 := by
  let lift : (X → ZMod 2) →ₗ[ZMod 2] S.toSubmodule := {
    toFun f := ⟨f,by rw [hS]; exact Submodule.mem_top⟩
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  let q := (Representation.Coinvariants.mk S.toRepresentation).comp lift
  have hq : Function.Surjective q := by
    intro a
    obtain ⟨m,hm⟩ := Representation.Coinvariants.mk_surjective S.toRepresentation a
    exact ⟨m.val,hm⟩
  have ht : ∀ (g : G) (f : X → ZMod 2),
      q (permutationFunctionRepresentation (ZMod 2) G X g f)=q f := by
    intro g f
    change Representation.Coinvariants.mk S.toRepresentation
      (S.toRepresentation g (lift f))=
        Representation.Coinvariants.mk S.toRepresentation (lift f)
    exact Representation.Coinvariants.mk_self_apply _ _ _
  rw [representationHead_finrank_eq_coinvariants]
  exact PermutationBinaryFourSection.trivial_quotient_finrank_le_one x q hq ht

/-- The head condition itself forces the original subspace dimension;
no premise that it is a hyperplane is used. -/
theorem dimension_eq_three_of_head_ge_two (x : X) (hcard : Nat.card X=4)
    (hhead : 2≤Module.finrank (ZMod 2)
      (S.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2)))) :
    Module.finrank (ZMod 2) S.toSubmodule=3 := by
  have hdim : Module.finrank (ZMod 2) (X → ZMod 2)=4 := by
    simpa only [Module.finrank_pi,Fintype.card_eq_nat_card] using hcard
  have hSle := Submodule.finrank_le S.toSubmodule
  rw [hdim] at hSle
  have hheadle := representationHead_finrank_le_dimension S.toRepresentation
  have hnsmall : ¬Module.finrank (ZMod 2) S.toSubmodule≤2 := by
    intro hsmall
    have he : Module.finrank (ZMod 2)
        (S.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2)))=
          Module.finrank (ZMod 2) S.toSubmodule := by omega
    have htriv := representation_trivial_of_head_finrank_eq S.toRepresentation he
    have htop : S.toRepresentation.invariants=⊤ := by
      apply top_unique
      intro v _ g
      exact htriv g v
    have hb := PermutationBinaryFourSection.subrepresentation_invariants_le_one x S
    rw [htop,finrank_top] at hb
    omega
  have hnlarge : Module.finrank (ZMod 2) S.toSubmodule≠4 := by
    intro he
    have htop : S.toSubmodule=⊤ := Submodule.eq_top_of_finrank_eq (he.trans hdim.symm)
    have hb := head_le_one_of_top S x htop
    omega
  omega

/-- A one-dimensional representation over the binary field is trivial.
This removes the unnecessary p-group hypothesis from the hyperplane
identification below. -/
theorem zmodTwo_representation_trivial_of_finrank_eq_one
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)
    (hdim : Module.finrank (ZMod 2) V = 1) :
    ∀ g v, ρ g v = v := by
  intro g
  obtain ⟨c, hc, _⟩ :=
    (ρ g).existsUnique_eq_smul_id_of_finrank_eq_one hdim
  have hc0 : c ≠ 0 := by
    intro hzero
    haveI : Nontrivial V := Module.nontrivial_of_finrank_pos
      (R := ZMod 2) (by omega)
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hinj : Function.Injective (ρ g) := by
      intro v w hvw
      have h := congrArg (ρ g⁻¹) hvw
      change (ρ g⁻¹ * ρ g) v = (ρ g⁻¹ * ρ g) w at h
      rw [← map_mul, inv_mul_cancel, map_one] at h
      exact h
    apply hv
    apply hinj
    rw [hc, hzero]
    simp
  have hc1 : c = 1 := Fin.eq_one_of_ne_zero c hc0
  rw [hc, hc1]
  simp

/-- A three-dimensional invariant subspace of the four-point binary
permutation module contains the full permutation-displacement kernel,
without any assumption on the acting group. -/
private theorem coinvariantsKer_le_of_dimension_three_unconditional
    (hcard : Nat.card X=4)
    (hS : Module.finrank (ZMod 2) S.toSubmodule=3) :
    Representation.Coinvariants.ker
        (permutationFunctionRepresentation (ZMod 2) G X) ≤ S.toSubmodule := by
  let ρ := PermutationBinaryFourSection.quotientRepresentation S
  have hdim : Module.finrank (ZMod 2) (X → ZMod 2)=4 := by
    simpa only [Module.finrank_pi,Fintype.card_eq_nat_card] using hcard
  have hsum := S.toSubmodule.finrank_quotient_add_finrank
  have hquot : Module.finrank (ZMod 2) ((X → ZMod 2) ⧸ S.toSubmodule)=1 := by
    rw [hS,hdim] at hsum
    omega
  have htrivial := zmodTwo_representation_trivial_of_finrank_eq_one ρ hquot
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨g,f⟩,rfl⟩
  apply (Submodule.Quotient.mk_eq_zero S.toSubmodule).mp
  change S.toSubmodule.mkQ
      (permutationFunctionRepresentation (ZMod 2) G X g f-f)=0
  rw [map_sub]
  change ρ g (S.toSubmodule.mkQ f) - S.toSubmodule.mkQ f = 0
  rw [htrivial, sub_self]

/-- A head of at least two identifies the literal augmentation hyperplane
for every transitive four-point action. -/
theorem eq_augmentation_of_head_ge_two_unconditional
    (x : X) (hcard : Nat.card X=4)
    (hhead : 2≤Module.finrank (ZMod 2)
      (S.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) G (ZMod 2)))) :
    Module.finrank (ZMod 2) S.toSubmodule=3 ∧
      S.toSubmodule=PermutationAugmentation.space (ZMod 2) X := by
  have hdim := dimension_eq_three_of_head_ge_two S x hcard hhead
  have hle := coinvariantsKer_le_of_dimension_three_unconditional S hcard hdim
  rw [PermutationAugmentation.coinvariantsKer_eq_space x] at hle
  have haug := PermutationAugmentation.space_finrank_add_one (k := ZMod 2) x
  refine ⟨hdim,?_⟩
  apply (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  omega

/-- The actual hyperplane quotient is trivial under the original binary
action. Hence every original permutation displacement belongs to S. -/
private theorem coinvariantsKer_le_of_dimension_three
    (hG : IsPGroup 2 G) (hcard : Nat.card X=4)
    (hS : Module.finrank (ZMod 2) S.toSubmodule=3) :
    Representation.Coinvariants.ker (permutationFunctionRepresentation (ZMod 2) G X)≤
      S.toSubmodule := by
  let ρ := PermutationBinaryFourSection.quotientRepresentation S
  have hdim : Module.finrank (ZMod 2) (X → ZMod 2)=4 := by
    simpa only [Module.finrank_pi,Fintype.card_eq_nat_card] using hcard
  have hsum := S.toSubmodule.finrank_quotient_add_finrank
  have hquot : Module.finrank (ZMod 2) ((X → ZMod 2) ⧸ S.toSubmodule)=1 := by
    rw [hS,hdim] at hsum
    omega
  letI : Finite ((X → ZMod 2) ⧸ S.toSubmodule) :=
    Finite.of_surjective S.toSubmodule.mkQ S.toSubmodule.mkQ_surjective
  letI : Nontrivial ((X → ZMod 2) ⧸ S.toSubmodule) :=
    Module.nontrivial_of_finrank_pos (R := ZMod 2) (by rw [hquot]; decide)
  obtain ⟨v,hv,hfixed⟩ := pGroup_representation_nonzero_fixed hG ρ
  have hne : ρ.invariants≠⊥ := by
    intro he
    have hm : v∈ρ.invariants := hfixed
    rw [he] at hm
    exact hv (by simpa only [Submodule.mem_bot] using hm)
  have hpos : 1≤Module.finrank (ZMod 2) ρ.invariants :=
    Submodule.one_le_finrank_iff.mpr hne
  have hle := Submodule.finrank_le ρ.invariants
  have htop : ρ.invariants=⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    change Module.finrank (ZMod 2) ρ.invariants=
      Module.finrank (ZMod 2) ((X → ZMod 2) ⧸ S.toSubmodule)
    omega
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨g,f⟩,rfl⟩
  apply (Submodule.Quotient.mk_eq_zero S.toSubmodule).mp
  have hf : S.toSubmodule.mkQ f∈ρ.invariants := by rw [htop]; exact Submodule.mem_top
  have he := hf g
  change S.toSubmodule.mkQ (permutationFunctionRepresentation (ZMod 2) G X g f)=
    S.toSubmodule.mkQ f at he
  change S.toSubmodule.mkQ (permutationFunctionRepresentation (ZMod 2) G X g f-f)=0
  rw [map_sub,he,sub_self]

/-- A head of at least two identifies the literal original augmentation
hyperplane, not merely an abstract three-dimensional isomorphic module. -/
theorem eq_augmentation_of_head_ge_two (hG : IsPGroup 2 G)
    (x : X) (hcard : Nat.card X=4)
    (hhead : 2≤Module.finrank (ZMod 2)
      (S.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2)))) :
    Module.finrank (ZMod 2) S.toSubmodule=3 ∧
      S.toSubmodule=PermutationAugmentation.space (ZMod 2) X := by
  have hdim := dimension_eq_three_of_head_ge_two S x hcard hhead
  have hle := coinvariantsKer_le_of_dimension_three S hG hcard hdim
  rw [PermutationAugmentation.coinvariantsKer_eq_space x] at hle
  have haug := PermutationAugmentation.space_finrank_add_one (k := ZMod 2) x
  refine ⟨hdim,?_⟩
  apply (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  omega

end PermutationBinaryFourAugmentation
end SymmetricSubgroupAsymptotics
