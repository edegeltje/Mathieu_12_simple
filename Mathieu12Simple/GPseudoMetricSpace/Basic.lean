import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Topology.Bornology.Basic
import Mathlib.Tactic

universe u v

variable {α:Type u} {β :Type v} [LinearOrderedCancelAddCommMonoid β]
@[ext]
class GDist (α : Type u) (β :Type v) [LinearOrderedCancelAddCommMonoid β] where
  gdist : α → α → β

open Set Filter Bornology
open scoped BigOperators Topology

-- create all bounded sets?
@[reducible]
def Bornology.ofGDist (gdist : α → α → β) (gdist_comm : ∀ x y, gdist x y = gdist y x)
    (gdist_triangle : ∀ x y z, gdist x z ≤ gdist x y + gdist y z) : Bornology α :=
  Bornology.ofBounded { s : Set α | ∃ C, ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → gdist x y ≤ C }
    ⟨0,fun x hx y => hx.elim⟩
    (fun s ⟨c, hc⟩ t h => ⟨c, fun x hx y hy => hc (h hx) (h hy)⟩)
    (fun s hs t ht => by
      rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
      · rwa [empty_union]
      rcases t.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
      · rwa [union_empty]
      rsuffices ⟨C, hC⟩ : ∃ C, ∀ z ∈ s ∪ t, gdist x z ≤ C
      · refine ⟨C + C, fun a ha b hb => (gdist_triangle a x b).trans ?_⟩
        simpa only [gdist_comm] using add_le_add (hC _ ha) (hC _ hb)
      rcases hs with ⟨Cs, hs⟩; rcases ht with ⟨Ct, ht⟩
      refine ⟨max Cs (gdist x y + Ct), fun z hz => hz.elim
        (fun hz => (hs hx hz).trans (le_max_left _ _))
        (fun hz => (gdist_triangle x y z).trans <|
          (add_le_add le_rfl (ht hy hz)).trans (le_max_right _ _))⟩)
    fun z => ⟨gdist z z, forall_eq.2 <| forall_eq.2 le_rfl⟩



class GPseudoMetricSpace (α : Type u) (β:Type v) [LinearOrderedCancelAddCommMonoid β] extends GDist α β where
  gdist_self : ∀ x : α, gdist x x = 0
  gdist_comm : ∀ x y : α, gdist x y = gdist y x
  gdist_triangle : ∀ x y z : α, gdist x z ≤ gdist x y + gdist y z
  toBornology : Bornology α := Bornology.ofGDist gdist gdist_comm gdist_triangle
  cobounded_sets : (Bornology.cobounded α).sets =
    { s | ∃ C : β, ∀ x ∈ sᶜ, ∀ y ∈ sᶜ, gdist x y ≤ C } := by intros; rfl

private theorem gdist_nonneg' {x y : α} (gdist : α → α → β)
    (gdist_self : ∀ x : α, gdist x x = 0) (gdist_comm : ∀ x y : α, gdist x y = gdist y x)
    (gdist_triangle : ∀ x y z : α, gdist x z ≤ gdist x y + gdist y z) : 0 ≤ gdist x y := by
  have : 0 ≤ gdist x y + gdist x y :=
    calc 0 = gdist x x := (gdist_self _).symm
    _ ≤ gdist x y + gdist y x := gdist_triangle _ _ _
    _ = gdist x y + gdist x y:= by rw [gdist_comm]
  exact nonneg_add_self_iff.mp this

@[ext]
theorem GPseudoMetricSpace.ext {m m' : GPseudoMetricSpace α β}
    (h : m.toGDist = m'.toGDist) : m = m' := by
  cases' m with d _ _ _ B hB
  cases' m' with d' _ _ _ B' hB'
  obtain rfl : d = d' := h
  congr
  · ext : 2
    rw [← Filter.mem_sets, ← Filter.mem_sets, hB, hB']

variable [GPseudoMetricSpace α β]

@[simp]
theorem gdist_self (x : α) : GDist.gdist x x = (0:β) :=
  GPseudoMetricSpace.gdist_self x

theorem gdist_comm (x y : α) : GDist.gdist x y = (GDist.gdist y x:β) :=
  GPseudoMetricSpace.gdist_comm x y

theorem gdist_triangle (x y z : α) : GDist.gdist x z ≤ (GDist.gdist x y + GDist.gdist y z:β) :=
  GPseudoMetricSpace.gdist_triangle x y z


theorem gdist_triangle_left (x y z : α) : GDist.gdist x y ≤ (GDist.gdist z x + GDist.gdist z y:β) := by
  rw [gdist_comm z]; apply gdist_triangle


theorem gdist_triangle_right (x y z : α) : GDist.gdist x y ≤ (GDist.gdist x z + GDist.gdist y z:β) := by
  rw [gdist_comm y]; apply gdist_triangle


theorem gdist_triangle4 (x y z w : α) : GDist.gdist x w ≤ (GDist.gdist x y + GDist.gdist y z + GDist.gdist z w:β) :=
  calc
    GDist.gdist x w ≤ GDist.gdist x z + GDist.gdist z w := gdist_triangle x z w
    _ ≤ (GDist.gdist x y + GDist.gdist y z + GDist.gdist z w:β) := add_le_add_right (gdist_triangle x y z) _


theorem gdist_triangle4_left (x₁ y₁ x₂ y₂ : α) :
    GDist.gdist x₂ y₂ ≤ (GDist.gdist x₁ y₁ + (GDist.gdist x₁ x₂ + GDist.gdist y₁ y₂):β ) := by
  rw [add_left_comm, gdist_comm x₁, ← add_assoc]
  apply gdist_triangle4


theorem gdist_triangle4_right (x₁ y₁ x₂ y₂ : α) :
    GDist.gdist x₁ y₁ ≤ (GDist.gdist x₁ x₂ + GDist.gdist y₁ y₂ + GDist.gdist x₂ y₂:β ) := by
  rw [add_right_comm, gdist_comm y₁]
  apply gdist_triangle4


/-- The triangle (polygon) inequality for sequences of points; `Finset.Ico` version. -/
theorem gdist_le_Ico_sum_dist (f : ℕ → α) {m n} (h : m ≤ n) :
    GDist.gdist (f m) (f n) ≤ (∑ i in Finset.Ico m n, GDist.gdist (f i) (f (i + 1)):β ) := by
  induction n, h using Nat.le_induction with
  | base => rw [Finset.Ico_self, Finset.sum_empty, gdist_self]
  | succ n hle ihn =>
    calc
      GDist.gdist (f m) (f (n + 1)) ≤ GDist.gdist (f m) (f n) + GDist.gdist (f n) (f (n + 1)) := gdist_triangle _ _ _
      _ ≤ (∑ i in Finset.Ico m n, _) + _ := add_le_add ihn le_rfl
      _ = ∑ i in Finset.Ico m (n + 1), _ := by
      { rw [Nat.Ico_succ_right_eq_insert_Ico hle, Finset.sum_insert, add_comm]; simp }


/-- The triangle (polygon) inequality for sequences of points; `Finset.range` version. -/
theorem gdist_le_range_sum_dist (f : ℕ → α) (n : ℕ) :
    GDist.gdist (f 0) (f n) ≤ (∑ i in Finset.range n, GDist.gdist (f i) (f (i + 1)) :β ) :=
  Nat.Ico_zero_eq_range ▸ gdist_le_Ico_sum_dist f (Nat.zero_le n)


/-- A version of `gdist_le_Ico_sum_dist` with each intermediate distance replaced
with an upper estimate. -/
theorem gdist_le_Ico_sum_of_dist_le {f : ℕ → α} {m n} (hmn : m ≤ n) {d : ℕ → β}
    (hd : ∀ {k}, m ≤ k → k < n → GDist.gdist (f k) (f (k + 1)) ≤ d k) :
    GDist.gdist (f m) (f n) ≤ ∑ i in Finset.Ico m n, d i :=
  le_trans (gdist_le_Ico_sum_dist f hmn) <|
    Finset.sum_le_sum fun _k hk => hd (Finset.mem_Ico.1 hk).1 (Finset.mem_Ico.1 hk).2


/-- A version of `gdist_le_range_sum_dist` with each intermediate distance replaced
with an upper estimate. -/
theorem gdist_le_range_sum_of_dist_le {f : ℕ → α} (n : ℕ) {d : ℕ → β}
    (hd : ∀ {k}, k < n → GDist.gdist (f k) (f (k + 1)) ≤ d k) :
    GDist.gdist (f 0) (f n) ≤ ∑ i in Finset.range n, d i :=
  Nat.Ico_zero_eq_range ▸ gdist_le_Ico_sum_of_dist_le (zero_le n) fun _ => hd


theorem swap_gdist : Function.swap GDist.gdist = (GDist.gdist:α → α → β) := by funext x y; exact gdist_comm _ _


theorem gdist_nonneg {x y : α} : 0 ≤ (GDist.gdist x y:β) :=
  gdist_nonneg' GDist.gdist gdist_self gdist_comm gdist_triangle

namespace GMetricSpace

-- instantiate pseudometric space as a topology
variable {x y z : α} {δ ε ε₁ ε₂ : β} {s : Set α}

/-- `ball x ε` is the set of all points `y` with `dist y x < ε` -/
def ball (x : α) (ε : β) : Set α :=
  { y | GDist.gdist y x < ε }


@[simp]
theorem mem_ball : y ∈ ball x ε ↔ GDist.gdist y x < ε :=
  Iff.rfl


theorem mem_ball' : y ∈ ball x ε ↔ GDist.gdist x y < ε := by rw [gdist_comm, mem_ball]


theorem pos_of_mem_ball (hy : y ∈ ball x ε) : 0 < ε :=
  gdist_nonneg.trans_lt hy


theorem mem_ball_self (h : 0 < ε) : x ∈ ball x ε := by
  rwa [mem_ball, gdist_self]


@[simp]
theorem nonempty_ball : (ball x ε).Nonempty ↔ 0 < ε :=
  ⟨fun ⟨_x, hx⟩ => pos_of_mem_ball hx, fun h => ⟨x, mem_ball_self h⟩⟩


@[simp]
theorem ball_eq_empty : ball x ε = ∅ ↔ ε ≤ 0 := by
  rw [← not_nonempty_iff_eq_empty, nonempty_ball, not_lt]


@[simp]
theorem ball_zero : ball x (0:β) = ∅ := by rw [ball_eq_empty]


/-- `closedBall x ε` is the set of all points `y` with `dist y x ≤ ε` -/
def closedBall (x : α) (ε : β) :=
  { y | GDist.gdist y x ≤ ε }


@[simp] theorem mem_closedBall : y ∈ closedBall x ε ↔ GDist.gdist y x ≤ ε := Iff.rfl


theorem mem_closedBall' : y ∈ closedBall x ε ↔ GDist.gdist x y ≤ ε := by rw [gdist_comm, mem_closedBall]


/-- `sphere x ε` is the set of all points `y` with `dist y x = ε` -/
def sphere (x : α) (ε : β) := { y | GDist.gdist y x = ε }


@[simp] theorem mem_sphere : y ∈ sphere x ε ↔ GDist.gdist y x = ε := Iff.rfl


theorem mem_sphere' : y ∈ sphere x ε ↔ GDist.gdist x y = ε := by rw [gdist_comm, mem_sphere]


theorem ne_of_mem_sphere (h : y ∈ sphere x ε) (hε : ε ≠ 0) : y ≠ x :=
  ne_of_mem_of_not_mem h <| by simpa using hε.symm


theorem nonneg_of_mem_sphere (hy : y ∈ sphere x ε) : 0 ≤ ε :=
  gdist_nonneg.trans_eq hy


@[simp]
theorem sphere_eq_empty_of_neg (hε : ε < 0) : sphere x ε = ∅ :=
  Set.eq_empty_iff_forall_not_mem.mpr fun _y hy => (nonneg_of_mem_sphere hy).not_lt hε


theorem sphere_eq_empty_of_subsingleton [Subsingleton α] (hε : ε ≠ 0) : sphere x ε = ∅ :=
  Set.eq_empty_iff_forall_not_mem.mpr fun _ h => ne_of_mem_sphere h hε (Subsingleton.elim _ _)


instance sphere_isEmpty_of_subsingleton [Subsingleton α] [NeZero ε] : IsEmpty (sphere x ε) := by
  rw [sphere_eq_empty_of_subsingleton (NeZero.ne ε)]; infer_instance


theorem mem_closedBall_self (h : 0 ≤ ε) : x ∈ closedBall x ε := by
  rwa [mem_closedBall, gdist_self]


@[simp]
theorem nonempty_closedBall : (closedBall x ε).Nonempty ↔ 0 ≤ ε :=
  ⟨fun ⟨_x, hx⟩ => gdist_nonneg.trans hx, fun h => ⟨x, mem_closedBall_self h⟩⟩


@[simp]
theorem closedBall_eq_empty : closedBall x ε = ∅ ↔ ε < 0 := by
  rw [← not_nonempty_iff_eq_empty, nonempty_closedBall, not_le]


/-- Closed balls and spheres coincide when the radius is non-positive -/
theorem closedBall_eq_sphere_of_nonpos (hε : ε ≤ 0) : closedBall x ε = sphere x ε :=
  Set.ext fun _ => (hε.trans gdist_nonneg).le_iff_eq


theorem ball_subset_closedBall : ball x ε ⊆ closedBall x ε := fun _y hy =>
  mem_closedBall.2 (le_of_lt hy)


theorem sphere_subset_closedBall : sphere x ε ⊆ closedBall x ε := fun _ => le_of_eq


lemma sphere_subset_ball {r R : β} (h : r < R) : sphere x r ⊆ ball x R := fun _x hx ↦
  (mem_sphere.1 hx).trans_lt h

theorem closedBall_disjoint_ball (h : δ + ε ≤ GDist.gdist x y) : Disjoint (closedBall x δ) (ball y ε) :=
  Set.disjoint_left.mpr fun _a ha1 ha2 =>
    (h.trans <| gdist_triangle_left _ _ _).not_lt <| add_lt_add_of_le_of_lt ha1 ha2

theorem ball_disjoint_closedBall (h : δ + ε ≤ GDist.gdist x y) : Disjoint (ball x δ) (closedBall y ε) :=
  (closedBall_disjoint_ball <| by rwa [add_comm, gdist_comm]).symm


theorem ball_disjoint_ball (h : δ + ε ≤ GDist.gdist x y) : Disjoint (ball x δ) (ball y ε) :=
  (closedBall_disjoint_ball h).mono_left ball_subset_closedBall


theorem closedBall_disjoint_closedBall (h : δ + ε < GDist.gdist x y) :
    Disjoint (closedBall x δ) (closedBall y ε) :=
  Set.disjoint_left.mpr fun _a ha1 ha2 =>
    h.not_le <| (gdist_triangle_left _ _ _).trans <| add_le_add ha1 ha2


theorem sphere_disjoint_ball : Disjoint (sphere x ε) (ball x ε) :=
  Set.disjoint_left.mpr fun _y hy₁ hy₂ => absurd hy₁ <| ne_of_lt hy₂


@[simp]
theorem ball_union_sphere : ball x ε ∪ sphere x ε = closedBall x ε :=
  Set.ext fun _y => (@le_iff_lt_or_eq β _ _ _).symm


@[simp]
theorem sphere_union_ball : sphere x ε ∪ ball x ε = closedBall x ε := by
  rw [union_comm, ball_union_sphere]


@[simp]
theorem closedBall_diff_sphere : closedBall x ε \ sphere x ε = ball x ε := by
  rw [← ball_union_sphere, Set.union_diff_cancel_right sphere_disjoint_ball.symm.le_bot]


@[simp]
theorem closedBall_diff_ball : closedBall x ε \ ball x ε = sphere x ε := by
  rw [← ball_union_sphere, Set.union_diff_cancel_left sphere_disjoint_ball.symm.le_bot]


theorem mem_ball_comm : x ∈ ball y ε ↔ y ∈ ball x ε := by rw [mem_ball', mem_ball]


theorem mem_closedBall_comm : x ∈ closedBall y ε ↔ y ∈ closedBall x ε := by
  rw [mem_closedBall', mem_closedBall]


theorem mem_sphere_comm : x ∈ sphere y ε ↔ y ∈ sphere x ε := by rw [mem_sphere', mem_sphere]


theorem ball_subset_ball (h : ε₁ ≤ ε₂) : ball x ε₁ ⊆ ball x ε₂ := fun _y yx =>
  lt_of_lt_of_le (mem_ball.1 yx) h


theorem closedBall_eq_bInter_ball : closedBall x ε = ⋂ δ > ε, ball x δ := by
  ext y; rw [mem_closedBall, ← forall_lt_iff_le', mem_iInter₂]; rfl


theorem ball_subset_ball' (h : ε₁ + GDist.gdist x y ≤ ε₂) : ball x ε₁ ⊆ ball y ε₂ := fun z hz =>
  calc
   GDist.gdist z y ≤ GDist.gdist z x + GDist.gdist x y := by apply gdist_triangle
    _ < ε₁ + GDist.gdist x y := by exact add_lt_add_right hz _
    _ ≤ ε₂ := h


theorem closedBall_subset_closedBall (h : ε₁ ≤ ε₂) : closedBall x ε₁ ⊆ closedBall x ε₂ :=
  fun _y (yx : _ ≤ ε₁) => le_trans yx h


theorem closedBall_subset_closedBall' (h : ε₁ + GDist.gdist x y ≤ ε₂) :
    closedBall x ε₁ ⊆ closedBall y ε₂ := fun z hz =>
  calc
    GDist.gdist z y ≤ GDist.gdist z x + GDist.gdist x y := gdist_triangle _ _ _
    _ ≤ ε₁ + GDist.gdist x y := add_le_add_right (mem_closedBall.1 hz) _
    _ ≤ ε₂ := h


theorem closedBall_subset_ball (h : ε₁ < ε₂) : closedBall x ε₁ ⊆ ball x ε₂ :=
  fun y (yh : GDist.gdist y x ≤ ε₁) => lt_of_le_of_lt yh h


theorem closedBall_subset_ball' (h : ε₁ + GDist.gdist x y < ε₂) :
    closedBall x ε₁ ⊆ ball y ε₂ := fun z hz =>
  calc
    GDist.gdist z y ≤ GDist.gdist z x + GDist.gdist x y := gdist_triangle _ _ _
    _ ≤ ε₁ + GDist.gdist x y := add_le_add_right (mem_closedBall.1 hz) _
    _ < ε₂ := h


theorem dist_le_add_of_nonempty_closedBall_inter_closedBall
    (h : (closedBall x ε₁ ∩ closedBall y ε₂).Nonempty) : GDist.gdist x y ≤ ε₁ + ε₂ :=
  let ⟨z, hz⟩ := h
  calc
    GDist.gdist x y ≤ GDist.gdist z x + GDist.gdist z y := gdist_triangle_left _ _ _
    _ ≤ ε₁ + ε₂ := add_le_add hz.1 hz.2


theorem dist_lt_add_of_nonempty_closedBall_inter_ball (h : (closedBall x ε₁ ∩ ball y ε₂).Nonempty) :
    GDist.gdist x y < ε₁ + ε₂ :=
  let ⟨z, hz⟩ := h
  calc
    GDist.gdist x y ≤ GDist.gdist z x + GDist.gdist z y := gdist_triangle_left _ _ _
    _ < ε₁ + ε₂ := add_lt_add_of_le_of_lt hz.1 hz.2


theorem dist_lt_add_of_nonempty_ball_inter_closedBall (h : (ball x ε₁ ∩ closedBall y ε₂).Nonempty) :
    GDist.gdist x y < ε₁ + ε₂ := by
  rw [inter_comm] at h
  rw [add_comm, gdist_comm]
  exact dist_lt_add_of_nonempty_closedBall_inter_ball h


theorem dist_lt_add_of_nonempty_ball_inter_ball (h : (ball x ε₁ ∩ ball y ε₂).Nonempty) :
    GDist.gdist x y < ε₁ + ε₂ :=
  dist_lt_add_of_nonempty_closedBall_inter_ball <|
    h.mono (inter_subset_inter ball_subset_closedBall Subset.rfl)
