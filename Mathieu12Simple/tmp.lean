import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Tactic

open Subgroup

open MulAction


namespace perm_stabilizer
variable {α: Type} {m: α}
def remainder (m: α) : Set α := (.≠ m)

theorem stabilizer_keeps_not_m (σ : stabilizer (Equiv.Perm α) m) (x:α): x ≠ m ↔ σ.val x ≠ m:= by
  obtain ⟨σ',hσ'⟩ := σ
  apply Iff.intro
  . contrapose!
    obtain ⟨τ,τ_inv,hτ1,hτ2⟩ := σ'
    dsimp
    intro h
    simp at hσ'
    rw [← hτ1 x,← hτ1 m,h,hσ']
  . contrapose!
    intro hx
    rw [hx]
    exact hσ'

theorem stabilizer_inv_keeps_not_m (σ : stabilizer (Equiv.Perm α) m) (x:α): x ≠ m ↔ σ.val.symm x ≠ m:= by
  nth_rw 1 [← σ.val.right_inv x]
  have h:= @stabilizer_keeps_not_m α m σ (σ.val.symm x)
  simp [h]


def stabilizer_to_map_remainder (σ : stabilizer (Equiv.Perm α) m) (x: remainder m) : remainder m :=
  {
    val := σ.val x
    property:= by
      suffices h : σ.val ↑x ≠ m
      . exact h
      rw [← stabilizer_keeps_not_m]
      exact x.property
  }
noncomputable def perm_remainder_to_map [DecidableEq α] (σ: Equiv.Perm (remainder m)): α → α:= fun x =>
  if hx : x = m
  then x
  else (σ ⟨x, hx⟩).val
  -- this is possibly problematic:
  -- the way this is written, the value of σ can be proof-dependent if there was no unilateral proof-equivalence.
  -- that might come back to bite us when proving properties of this function.

noncomputable def perm_remainder_map_is_perm (σ: Equiv.Perm (remainder m)) : Equiv.Perm α := {
  toFun := fun x => by
    by_cases hx: x = m
    . exact m
    . exact (σ ⟨x, hx⟩).val
  invFun := fun y => by
    by_cases hy : y = m
    . exact m
    . exact (σ.invFun ⟨y,hy⟩).val
  left_inv := by
    intro x
    simp
    split
    . simp [*]
    . simp [*]
      apply dif_neg
      simp [*]
      exact (σ ⟨x,_⟩).property

  right_inv := by
    intro y
    simp only [Equiv.invFun_as_coe]
    split
    . simp [*]
    . simp [*]
      apply dif_neg
      simp [*]
      exact (σ.symm ⟨y,_⟩).property
}
lemma remainder_perm_mem_stabiliser (σ : Equiv.Perm (remainder m)) : perm_remainder_map_is_perm σ ∈ stabilizer (Equiv.Perm α) m := by
  simp [perm_remainder_map_is_perm]

def stabilizer_to_remainder_perm (σ : stabilizer (Equiv.Perm α) m) : Equiv.Perm (remainder m) :={
  toFun := fun x => {
      val := σ.val x,
      property:= by
        suffices h : σ.val ↑x ≠ m
        . exact h
        rw [← stabilizer_keeps_not_m]
        exact x.property
    }
  invFun := fun y => {
    val := σ.val.invFun y
    property:= by
      suffices h: σ.val.symm ↑y ≠ m
      . exact h
      rw [← stabilizer_inv_keeps_not_m]
      exact y.property
    }
  left_inv := by
    intro x
    simp only [Equiv.toFun_as_coe, Equiv.invFun_as_coe, Equiv.symm_apply_apply, Subtype.coe_eta]
  right_inv := by
    intro x
    simp only [Equiv.invFun_as_coe, Equiv.toFun_as_coe, Equiv.apply_symm_apply, Subtype.coe_eta]
}

theorem stabiliser_is_permutations_of_remainder: stabilizer (Equiv.Perm α) m ≃* Equiv.Perm (remainder m) where
  toFun := stabilizer_to_remainder_perm
  invFun := fun σ => ⟨perm_remainder_map_is_perm σ,remainder_perm_mem_stabiliser σ⟩
  left_inv := by
    intro σ
    ext x
    dsimp
    rw [perm_remainder_map_is_perm, stabilizer_to_remainder_perm]
    simp [*]
    split
    . simp [*]
      rw [← @Equiv.Perm.smul_def, σ.property]
    . rfl
  right_inv := by
    intro σ
    ext y
    dsimp
    rw [stabilizer_to_remainder_perm]
    simp
    rw [perm_remainder_map_is_perm]
    simp
    split
    . have hcontra: ↑y ≠ m
      . exact y.property
      contradiction
    . rfl
  map_mul' := by
    intro x y
    ext
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    exact rfl

end perm_stabilizer
