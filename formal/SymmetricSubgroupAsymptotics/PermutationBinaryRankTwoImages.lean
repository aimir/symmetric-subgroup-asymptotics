import SymmetricSubgroupAsymptotics.PermutationBinaryRankTwoOrbits
import SymmetricSubgroupAsymptotics.PermutationBinaryOrbitSection

/-! The two actual orbit images in the common-character residual.

The full original correlated permutation subrepresentation has a trivial
quotient of dimension four under the original action kernel. Coordinate
head filtration therefore excludes a cyclic-transitive element on either
of its two four-point orbits. The action on the other orbit is still by
the entire original kernel, not by that cyclic lift. The resulting actual
orbit images have order four and exponent two. No splitting of the
original module across its two orbit coordinates is assumed.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics

section NoCyclicOrbit

variable {k G X A : Type} [Field k] [Group G] [Finite G]
    [MulAction G X] [Finite X] [AddCommGroup A] [Module k A]
    [FiniteDimensional k A]

/-- A cyclic-transitive element on one original coordinate would give
head bound one there. The other original coordinate has whole-group
head bound two, contradicting the actual four-dimensional quotient. -/
theorem binary_two_orbit_trivial_section_no_cyclic_transitive
    (hG : IsPGroup 2 G)
    (hclasses : Nat.card (MulAction.orbitRel.Quotient G X)=2)
    (hcard : ∀ o : MulAction.orbitRel.Quotient G X, Nat.card o.orbit=4)
    (M : Subrepresentation (permutationFunctionRepresentation k G X))
    (q : M.toSubmodule →ₗ[k] A) (hq : Function.Surjective q)
    (htrivial : ∀ (g : G) (m : M.toSubmodule), q (M.toRepresentation g m)=q m)
    (hA : 4≤Module.finrank k A)
    (o₀ : MulAction.orbitRel.Quotient G X) (g : G) :
    ¬MulAction.IsPretransitive (Subgroup.zpowers g) o₀.orbit := by
  intro hcyclic
  letI := hcyclic
  let x₀ : o₀.orbit := ⟨o₀.nonempty_orbit.choose,o₀.nonempty_orbit.choose_spec⟩
  letI : Nonempty (MulAction.orbitRel.Quotient (Subgroup.zpowers g) o₀.orbit) :=
    ⟨Quotient.mk'' x₀⟩
  letI : Subsingleton (MulAction.orbitRel.Quotient (Subgroup.zpowers g) o₀.orbit) :=
    (MulAction.pretransitive_iff_subsingleton_quotient _ _).mp hcyclic
  have hcyclicCard :
      Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers g) o₀.orbit)=1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨inferInstance,inferInstance⟩
  let b : MulAction.orbitRel.Quotient G X → ℕ := fun o => if o=o₀ then 1 else 2
  have hhead : Module.finrank k (M.toRepresentation.IntertwiningMap
      (Representation.trivial k G k))≤∑ o,b o := by
    apply representationHom_finrank_le_coordinates
      (fun o : MulAction.orbitRel.Quotient G X => o.orbit → k)
      M.toRepresentation (fun o => permutationFunctionRepresentation k G o.orbit)
      (Representation.trivial k G k) b ?_
      (permutationSubrepresentationOrbitRestriction M)
      (permutationSubrepresentationOrbitRestriction_jointly_injective M)
    intro o S
    by_cases ho : o=o₀
    · subst o
      simpa only [b,if_pos rfl,hcyclicCard] using
        (permutation_subrepresentationHead_le_cyclicOrbitCount S g)
    · let x : o.orbit := ⟨o.nonempty_orbit.choose,o.nonempty_orbit.choose_spec⟩
      have hb := twoGroup_permutationSubrepresentationHead_le_width hG 2
        (by simpa using hcard o) x S
      norm_num at hb
      simpa only [b,if_neg ho] using hb
  let q' : M.toRepresentation.Coinvariants →ₗ[k] A :=
    Representation.Coinvariants.lift M.toRepresentation q (by
      intro g
      apply LinearMap.ext
      exact htrivial g)
  have hq' : Function.Surjective q' := by
    intro a
    obtain ⟨m,rfl⟩ := hq a
    exact ⟨Representation.Coinvariants.mk M.toRepresentation m,rfl⟩
  have hdim := LinearMap.finrank_le_finrank_of_surjective hq'
  rw [← representationHead_finrank_eq_coinvariants] at hdim
  have hsum : (∑ o,b o)+1=4 := by
    calc
      (∑ o,b o)+1 = (∑ o,b o)+∑ o,if o=o₀ then 1 else 0 := by simp
      _ = ∑ o,(b o+(if o=o₀ then 1 else 0)) := Finset.sum_add_distrib.symm
      _ = ∑ _ : MulAction.orbitRel.Quotient G X,2 := by
        apply Finset.sum_congr rfl
        intro o _
        by_cases ho : o=o₀ <;> simp [b,ho]
      _ = 4 := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
          Fintype.card_eq_nat_card,hclasses]
        norm_num
  omega

end NoCyclicOrbit

section FourPointAction

variable {G X : Type} [Group G] [Finite G] [MulAction G X] [Finite X]

/-- On four original points, absence of a cyclic-transitive element in
a binary action forces every original permutation to square to identity.
The original group itself may have a nontrivial action kernel. -/
theorem binary_four_action_pow_two (hG : IsPGroup 2 G) (hcard : Nat.card X=4)
    (hcyclic : ∀ g : G, ¬MulAction.IsPretransitive (Subgroup.zpowers g) X)
    (g : G) (x : X) : g^2 • x=x := by
  have hle : Nat.card (MulAction.orbit (Subgroup.zpowers g) x)≤4 := by
    exact (Nat.card_le_card_of_injective
      (fun y : MulAction.orbit (Subgroup.zpowers g) x => (y:X))
      Subtype.val_injective).trans_eq hcard
  have hne : Nat.card (MulAction.orbit (Subgroup.zpowers g) x)≠4 := by
    intro he
    have hsurj : Function.Surjective
        (fun y : MulAction.orbit (Subgroup.zpowers g) x => (y:X)) :=
      ((Nat.bijective_iff_injective_and_card _).mpr
        ⟨Subtype.val_injective,he.trans hcard.symm⟩).2
    apply hcyclic g
    refine ⟨?_⟩
    intro y z
    obtain ⟨y',hy'⟩ := hsurj y
    obtain ⟨z',hz'⟩ := hsurj z
    obtain ⟨a,ha⟩ := y'.property
    obtain ⟨b,hb⟩ := z'.property
    change (y':X)=y at hy'
    change (z':X)=z at hz'
    change a • x=(y':X) at ha
    change b • x=(z':X) at hb
    refine ⟨b*a⁻¹,?_⟩
    rw [← hy',← hz',← ha,← hb,mul_smul,inv_smul_smul]
  obtain ⟨n,hn⟩ := (hG.to_subgroup (Subgroup.zpowers g)).card_orbit x
  have hnle : n≤1 := by
    by_contra hnle
    have hpow : 2^2≤2^n := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hsize : Nat.card (MulAction.orbit (Subgroup.zpowers g) x)=1 ∨
      Nat.card (MulAction.orbit (Subgroup.zpowers g) x)=2 := by
    interval_cases n <;> norm_num at hn ⊢ <;> omega
  have hindex : (MulAction.stabilizer (Subgroup.zpowers g) x).index=
      Nat.card (MulAction.orbit (Subgroup.zpowers g) x) :=
    (Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (Subgroup.zpowers g) x)).symm
  let a : Subgroup.zpowers g := ⟨g,Subgroup.mem_zpowers g⟩
  have hm := Subgroup.pow_index_mem (MulAction.stabilizer (Subgroup.zpowers g) x) a
  have hf := MulAction.mem_stabilizer_iff.mp hm
  rw [hindex] at hf
  rcases hsize with hsize | hsize
  · rw [hsize,pow_one] at hf
    change g • x=x at hf
    rw [pow_two,mul_smul,hf,hf]
  · rw [hsize] at hf
    exact hf

/-- A transitive action whose actual permutations all square to one has
an actual regular image. Evaluation at the original point is bijective;
there is no choice of an isomorphic replacement permutation group. -/
theorem transitive_image_regular_of_pow_two [MulAction.IsPretransitive G X]
    (x : X) (hsquare : ∀ (g : G) (y : X),g^2 • y=y) :
    Nat.card (MulAction.toPermHom G X).range=Nat.card X ∧
      (∀ t : (MulAction.toPermHom G X).range,t^2=1) ∧
      ∀ y : X,MulAction.stabilizer (MulAction.toPermHom G X).range y=⊥ := by
  let T := (MulAction.toPermHom G X).range
  have hsq : ∀ t : T,t^2=1 := by
    rintro ⟨t,⟨g,rfl⟩⟩
    apply Subtype.ext
    apply Equiv.ext
    intro y
    change ((MulAction.toPermHom G X g)^2) y=y
    rw [← map_pow]
    exact hsquare g y
  have hinv : ∀ t : T,t⁻¹=t := fun t =>
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hsq t)
  have hcomm : ∀ s t : T,s*t=t*s := by
    intro s t
    calc
      s*t = (s*t)⁻¹ := (hinv _).symm
      _ = t⁻¹*s⁻¹ := mul_inv_rev _ _
      _ = t*s := by rw [hinv,hinv]
  have heval : ∀ y : X,Function.Injective (fun t : T => t.val y) := by
    intro y s t he
    apply Subtype.ext
    apply Equiv.ext
    intro z
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G y z
    let a : T := (MulAction.toPermHom G X).rangeRestrict g
    have ha : a.val y=z := hg
    calc
      s.val z = (s*a).val y := by rw [← ha]; rfl
      _ = (a*s).val y := congrArg (fun u : T => u.val y) (hcomm s a)
      _ = a.val (s.val y) := rfl
      _ = a.val (t.val y) := congrArg a.val he
      _ = (a*t).val y := rfl
      _ = (t*a).val y := congrArg (fun u : T => u.val y) (hcomm a t)
      _ = t.val z := by rw [← ha]; rfl
  have hsurj : Function.Surjective (fun t : T => t.val x) := by
    intro y
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G x y
    exact ⟨(MulAction.toPermHom G X).rangeRestrict g,hg⟩
  refine ⟨Nat.card_congr (Equiv.ofBijective _ ⟨heval x,hsurj⟩),hsq,?_⟩
  intro y
  apply le_antisymm ?_ bot_le
  intro t ht
  apply Subgroup.mem_bot.mpr
  apply heval y
  exact MulAction.mem_stabilizer_iff.mp ht

end FourPointAction

section ActualResidual

variable {G X A : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [MulAction.IsPretransitive G X]
    [AddCommGroup A] [Module (ZMod 2) A] [FiniteDimensional (ZMod 2) A]

/-- Both orbit images of the literal common-character kernel are regular
elementary abelian groups of order four. All restrictions are from the
original correlated module; no coordinate-product equality is an input. -/
theorem permutationBinary_twoBlockCharacter_regular_orbit_images
    (hG : IsPGroup 2 G) (x : X) (hX : Nat.card X=8)
    (ρ : Representation (ZMod 2) G A)
    (M : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G X))
    (q : M.toRepresentation.IntertwiningMap ρ) (hq : Function.Surjective q)
    (hA : Module.finrank (ZMod 2) A=4)
    (data : RepresentationBinaryCommonCharacter.TwoBlockCharacter ρ)
    (o : MulAction.orbitRel.Quotient ρ.ker X) :
    Nat.card (MulAction.toPermHom ρ.ker o.orbit).range=4 ∧
      (∀ t : (MulAction.toPermHom ρ.ker o.orbit).range,t^2=1) ∧
      ∀ y : o.orbit,MulAction.stabilizer (MulAction.toPermHom ρ.ker o.orbit).range y=⊥ := by
  obtain ⟨hclasses,hcard⟩ := permutationBinary_twoBlockCharacter_orbits hG x hX ρ M q hq hA data
  let MK : Subrepresentation (permutationFunctionRepresentation (ZMod 2) ρ.ker X) := {
    toSubmodule := M.toSubmodule
    apply_mem_toSubmodule := fun g _ hm => M.apply_mem_toSubmodule (g:G) hm }
  have htrivial : ∀ (g : ρ.ker) (m : MK.toSubmodule),
      q (MK.toRepresentation g m)=q m := by
    intro g m
    change q (M.toRepresentation (g:G) m)=q m
    rw [Representation.IntertwiningMap.isIntertwining _ _ q]
    have hg : ρ (g:G)=1 := g.property
    rw [hg]
    rfl
  have hcyclic : ∀ g : ρ.ker,¬MulAction.IsPretransitive (Subgroup.zpowers g) o.orbit :=
    fun g => binary_two_orbit_trivial_section_no_cyclic_transitive
      (hG.to_subgroup ρ.ker) hclasses hcard MK q.toLinearMap hq htrivial hA.ge o g
  let y : o.orbit := ⟨o.nonempty_orbit.choose,o.nonempty_orbit.choose_spec⟩
  obtain ⟨hc,hs,hreg⟩ := transitive_image_regular_of_pow_two y
    (binary_four_action_pow_two (hG.to_subgroup ρ.ker) (hcard o) hcyclic)
  exact ⟨hc.trans (hcard o),hs,hreg⟩

end ActualResidual

end SymmetricSubgroupAsymptotics
