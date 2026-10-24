import SymmetricSubgroupAsymptotics.CentralExtensionLayerOrbitIndex
import Mathlib.GroupTheory.GroupAction.ConjAct

/-! Index and layer orbits for an actual normal subgroup, without a chosen
complement or a semidirect-product recognition. The subgroup preserving a
layer is always the same join `M ⊔ N`; its index is coupled to the literal
intersection `M.comap N.subtype`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.ActualNormalLayerOrbitIndex

variable {P : Type*} [Group P] [Finite P]

/-- The actual quotient map, rather than a split extension, gives the
normal-subgroup index factorization. -/
theorem index_factor (N M : Subgroup P) [N.Normal] :
    M.index = (M.comap N.subtype).index * (M ⊔ N).index := by
  let f : P →* P ⧸ N := QuotientGroup.mk' N
  have h := CFSGKernelIndexFactor.index_eq_kernel_relIndex_mul_map_index
    f (QuotientGroup.mk'_surjective N) M
  have hk : f.ker = N := QuotientGroup.ker_mk' N
  have hi : (M.map f).index = (M ⊔ N).index := by
    rw [Subgroup.index_map, hk,
      f.range_eq_top_of_surjective (QuotientGroup.mk'_surjective N),
      Subgroup.index_top, mul_one]
  rw [hk, hi] at h
  exact h

/-- Exact counting retains the same radical intersection and join index. -/
theorem index_mul_intersection_card (N M : Subgroup P) [N.Normal] :
    M.index * Nat.card (M.comap N.subtype) =
      Nat.card N * (M ⊔ N).index := by
  rw [index_factor N M]
  calc
    (M.comap N.subtype).index * (M ⊔ N).index *
        Nat.card (M.comap N.subtype) =
        ((M.comap N.subtype).index * Nat.card (M.comap N.subtype)) *
          (M ⊔ N).index := by ring
    _ = _ := by rw [Subgroup.index_mul_card]

/-- Exact splitting through the central and abelian layers of the same
intersection. This does not assert that the ambient extension splits. -/
theorem index_layer_factor {V Z : Type*} [Group V] [Group Z] [Finite V]
    (N M : Subgroup P) [N.Normal]
    (π : N →* V) (hπ : Function.Surjective π) (ι : Z →* N)
    (hexact : ι.range = π.ker) :
    M.index = ((M.comap N.subtype).comap ι).index *
      ((M.comap N.subtype).map π).index * (M ⊔ N).index := by
  have h := CFSGKernelIndexFactor.index_eq_kernel_relIndex_mul_map_index
    π hπ (M.comap N.subtype)
  have hc : ((M.comap N.subtype).comap ι).index =
      (M.comap N.subtype).relIndex π.ker := by
    rw [Subgroup.index_comap, hexact]
  rw [← hc] at h
  rw [index_factor N M, h]

/-- All three factors refer to one literal subgroup and one join. -/
theorem index_mul_layer_cards {V Z : Type*} [Group V] [Group Z]
    [Finite V] [Finite Z]
    (N M : Subgroup P) [N.Normal]
    (π : N →* V) (hπ : Function.Surjective π) (ι : Z →* N)
    (hexact : ι.range = π.ker) :
    M.index * Nat.card ((M.comap N.subtype).comap ι) *
      Nat.card ((M.comap N.subtype).map π) =
        Nat.card Z * Nat.card V * (M ⊔ N).index := by
  rw [index_layer_factor N M π hπ ι hexact]
  calc
    _ = (Nat.card ((M.comap N.subtype).comap ι) *
          ((M.comap N.subtype).comap ι).index) *
        (Nat.card ((M.comap N.subtype).map π) *
          ((M.comap N.subtype).map π).index) * (M ⊔ N).index := by ring
    _ = _ := by rw [Subgroup.card_mul_index, Subgroup.card_mul_index]

/-- An action trivial on the actual normal subgroup extends invariance
from `M` to `M ⊔ N`. No complement needs to be constructed. -/
theorem invariant_sup_of_normal_trivial {X : Type*} [MulAction P X]
    (N M : Subgroup P) [N.Normal] (A : Set X)
    (hN : ∀ n ∈ N, ∀ x : X, n • x = x)
    (hM : ∀ m ∈ M, ∀ x ∈ A, m • x ∈ A) :
    ∀ p ∈ M ⊔ N, ∀ x ∈ A, p • x ∈ A := by
  intro p hp x hx
  obtain ⟨m, hm, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hp
  rw [mul_smul, hN n hn]
  exact hM m hm x hx

variable {V : Type*} [CommGroup V]

/-- The literal image of the radical intersection in an abelian quotient
is invariant under the join, even when the intersection itself is not. -/
theorem quotient_layer_invariant (N M : Subgroup P) [N.Normal]
    (π : N →* V) (hπ : Function.Surjective π)
    (ψ : P →* MulAut V)
    (hequiv : ∀ p n, π (MulAut.conjNormal p n) = ψ p (π n)) :
    ∀ p ∈ M ⊔ N, ∀ v ∈ (M.comap N.subtype).map π,
      ψ p v ∈ (M.comap N.subtype).map π := by
  letI : MulAction P V := MulAction.compHom V ψ
  apply invariant_sup_of_normal_trivial N M
    (((M.comap N.subtype).map π : Subgroup V) : Set V)
  · intro n hn v
    obtain ⟨a, rfl⟩ := hπ v
    change ψ n (π a) = π a
    rw [← hequiv]
    have hconj : MulAut.conjNormal n a = ⟨n, hn⟩ * a * ⟨n, hn⟩⁻¹ :=
      Subtype.ext rfl
    rw [hconj, map_mul, map_mul, map_inv]
    simp [mul_comm]
  · intro m hm v hv
    obtain ⟨a, ha, rfl⟩ := hv
    refine ⟨MulAut.conjNormal m a, ?_, hequiv m a⟩
    change m * (a : P) * m⁻¹ ∈ M
    exact M.mul_mem (M.mul_mem hm ha) (M.inv_mem hm)

/-- A nonidentity quotient-layer vector pays its orbit with that same
join index and literal intersection image. -/
theorem quotient_orbit_card_le [Finite V]
    (N M : Subgroup P) [N.Normal]
    (π : N →* V) (hπ : Function.Surjective π)
    (ψ : P →* MulAut V)
    (hequiv : ∀ p n, π (MulAut.conjNormal p n) = ψ p (π n))
    (v : V) (hv : v ∈ (M.comap N.subtype).map π) (hv1 : v ≠ 1) :
    Nat.card (CentralExtensionLayerOrbitIndex.layerOrbit ψ v) ≤
      (Nat.card ((M.comap N.subtype).map π) - 1) * (M ⊔ N).index :=
  CentralExtensionLayerOrbitIndex.orbit_card_le ψ (M ⊔ N)
    ((M.comap N.subtype).map π)
    (quotient_layer_invariant N M π hπ ψ hequiv) v hv hv1

variable {Z : Type*} [Group Z]

/-- Centrality removes conjugation by `N` only on the central layer.
The intersection with that layer can still be diagonal. -/
theorem central_layer_invariant (N M : Subgroup P) [N.Normal]
    (ι : Z →* N) (hι : Function.Injective ι)
    (hcentral : ∀ z, ι z ∈ Subgroup.center N)
    (χ : P →* MulAut Z)
    (hequiv : ∀ p z, ι (χ p z) = MulAut.conjNormal p (ι z)) :
    ∀ p ∈ M ⊔ N, ∀ z ∈ (M.comap N.subtype).comap ι,
      χ p z ∈ (M.comap N.subtype).comap ι := by
  letI : MulAction P Z := MulAction.compHom Z χ
  apply invariant_sup_of_normal_trivial N M
    ((((M.comap N.subtype).comap ι : Subgroup Z) : Set Z))
  · intro n hn z
    change χ n z = z
    apply hι
    rw [hequiv]
    have hc := (Subgroup.mem_center_iff.mp (hcentral z)) (⟨n, hn⟩ : N)
    apply Subtype.ext
    change n * ((ι z : N) : P) * n⁻¹ = _
    have hc' : n * ((ι z : N) : P) = ((ι z : N) : P) * n :=
      congrArg (fun a : N => (a : P)) hc
    rw [hc', mul_assoc, mul_inv_cancel, mul_one]
  · intro m hm z hz
    change ((ι (χ m z) : N) : P) ∈ M
    rw [hequiv]
    change m * ((ι z : N) : P) * m⁻¹ ∈ M
    exact M.mul_mem (M.mul_mem hm hz) (M.inv_mem hm)

theorem central_orbit_card_le [Finite Z]
    (N M : Subgroup P) [N.Normal]
    (ι : Z →* N) (hι : Function.Injective ι)
    (hcentral : ∀ z, ι z ∈ Subgroup.center N)
    (χ : P →* MulAut Z)
    (hequiv : ∀ p z, ι (χ p z) = MulAut.conjNormal p (ι z))
    (z : Z) (hz : z ∈ (M.comap N.subtype).comap ι) (hz1 : z ≠ 1) :
    Nat.card (CentralExtensionLayerOrbitIndex.layerOrbit χ z) ≤
      (Nat.card ((M.comap N.subtype).comap ι) - 1) * (M ⊔ N).index :=
  CentralExtensionLayerOrbitIndex.orbit_card_le χ (M ⊔ N)
    ((M.comap N.subtype).comap ι)
    (central_layer_invariant N M ι hι hcentral χ hequiv) z hz hz1

end SymmetricSubgroupAsymptotics.ActualNormalLayerOrbitIndex
