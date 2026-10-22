import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularTransport

/-! The proved triple parity defines a genuine component stabilizer
inside the actual linear isometry group. Its subgroup laws are proved
from intersection transport and the alternating-triangle parity, not
postulated as a Dickson classification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularComponents
open CFSGOrthogonalDIndexSingularParity CFSGOrthogonalDIndexSingularTransport
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

def distance (r : ℕ) (P L : Submodule K V) : ℕ := r - Module.finrank K ↥(P ⊓ L)

theorem even_of_even_three {a b c : ℕ} (ht : Even (a + b + c))
    (ha : Even a) (hb : Even b) : Even c := by
  obtain ⟨t, ht⟩ := ht
  obtain ⟨u, hu⟩ := ha
  obtain ⟨v, hv⟩ := hb
  exact ⟨t - u - v, by omega⟩

theorem same_component_trans [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (r : ℕ) (hV : Module.finrank K V = 2 * r)
    (P L M : Submodule K V)
    (hP : LinearMap.BilinForm.orthogonal Q.polarBilin P = P)
    (hL : LinearMap.BilinForm.orthogonal Q.polarBilin L = L)
    (hM : LinearMap.BilinForm.orthogonal Q.polarBilin M = M)
    (hzP : ∀ x : P, Q (x : V) = 0) (hzL : ∀ x : L, Q (x : V) = 0)
    (hzM : ∀ x : M, Q (x : V) = 0)
    (hPL : Even (distance r P L)) (hLM : Even (distance r L M)) :
    Even (distance r P M) :=
  even_of_even_three
    (even_three_distances Q hQ r hV P L M hP hL hM hzP hzL hzM) hPL hLM

def isometryGroup (Q : QuadraticForm K V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {f | ∀ x, Q (f x) = Q x}
  one_mem' := fun _ => rfl
  mul_mem' {f g} hf hg x := by
    change Q (f (g x)) = Q x
    rw [hf, hg]
  inv_mem' {f} hf x := by
    change Q (f.symm x) = Q x
    simpa only [f.apply_symm_apply] using (hf (f.symm x)).symm

def componentStabilizer [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (r : ℕ) (hV : Module.finrank K V = 2 * r)
    (P : Submodule K V) (hP : LinearMap.BilinForm.orthogonal Q.polarBilin P = P)
    (hzP : ∀ x : P, Q (x : V) = 0) : Subgroup (isometryGroup Q) where
  carrier := {f | Even (distance r P (P.map f.val.toLinearMap))}
  one_mem' := by
    have hmap : P.map (1 : V ≃ₗ[K] V).toLinearMap = P := Submodule.map_id P
    change Even (r - Module.finrank K ↥(P ⊓ P.map (1 : V ≃ₗ[K] V).toLinearMap))
    rw [hmap, inf_idem, self_orthogonal_finrank Q.polarBilin hQ r hV P hP, Nat.sub_self]
    exact ⟨0, rfl⟩
  mul_mem' {f g} hf hg := by
    let Pf := P.map f.val.toLinearMap
    let Pg := P.map g.val.toLinearMap
    let Pfg := P.map (f.val * g.val).toLinearMap
    have hfg : Pg.map f.val.toLinearMap = Pfg := by
      rw [← Submodule.map_comp]
      rfl
    have hd : distance r Pf Pfg = distance r P Pg := by
      change r - Module.finrank K ↥(Pf ⊓ Pfg) = r - Module.finrank K ↥(P ⊓ Pg)
      rw [← hfg]
      exact congrArg (fun a : ℕ => r - a) (intersection_map_finrank f.val P Pg)
    have hPf := map_self_orthogonal Q f.val f.property P hP
    have hPfg := map_self_orthogonal Q (f.val * g.val) (f * g).property P hP
    have hzPf := map_singular Q f.val f.property P hzP
    have hzPfg := map_singular Q (f.val * g.val) (f * g).property P hzP
    apply same_component_trans Q hQ r hV P Pf Pfg hP hPf hPfg hzP hzPf hzPfg hf
    rw [hd]
    exact hg
  inv_mem' {f} hf := by
    let Pi := P.map (f.val⁻¹).toLinearMap
    have hmap : Pi.map f.val.toLinearMap = P := by
      rw [← Submodule.map_comp]
      have he : f.val.toLinearMap.comp (f.val⁻¹).toLinearMap = LinearMap.id := by
        apply LinearMap.ext
        intro x
        exact f.val.apply_symm_apply x
      rw [he, Submodule.map_id]
    have hd := intersection_map_finrank f.val P Pi
    rw [hmap] at hd
    change Even (r - Module.finrank K ↥(P ⊓ Pi))
    rw [← hd, inf_comm]
    exact hf

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularComponents
