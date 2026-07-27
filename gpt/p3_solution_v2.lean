import Mathlib
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace LiuBangXiangYu

/-- The multiset of piece lengths obtained by cutting `[0,1]` at the points of a
finite set `S ⊆ (0,1)`.  We sort `S` ascending, prepend `0` and append `1`, and
take consecutive differences.  The result is a list of `|S| + 1` positive reals
summing to `1` (when `S ⊆ (0,1)`). -/
noncomputable def pieceLengths (S : Finset ℝ) : List ℝ :=
  let l : List ℝ := (0 : ℝ) :: (S.sort (· ≤ ·)) ++ [1]
  List.zipWith (fun a b => b - a) l l.tail

/-- The sum of the entries of a list `L` at the (0-indexed) even positions, after
sorting `L` in non-increasing order.  These are the entries in the `1`st, `3`rd,
`5`th, … positions of the sorted (decreasing) list, i.e. the pieces claimed by
the first mover under the greedy claiming rule. -/
noncomputable def firstPlayerShare (L : List ℝ) : ℝ :=
  let sorted := L.mergeSort (· ≥ ·)
  ((sorted.zipIdx.filter (fun p => p.2 % 2 = 0)).map (fun p => p.1)).sum

/-- `L(A,B)`: Liu Bang's total length, given Liu Bang's marks `A` and Xiang Yu's
marks `B`. -/
noncomputable def L (A B : Finset ℝ) : ℝ :=
  firstPlayerShare (pieceLengths (A ∪ B))

/-- The set of admissible markings for a player: a finite subset of `(0,1)` of
size at most `n`.  We encode it as a `Finset ℝ` subject to the side conditions. -/
def AdmissibleMark (n : ℕ) (X : Finset ℝ) : Prop :=
  (↑X ⊆ Set.Ioo (0 : ℝ) 1) ∧ X.card ≤ n

/-- The value Liu Bang can guarantee.

`V n` is the supremum over Liu Bang's admissible markings `A` of the infimum,
over Xiang Yu's admissible markings `B` disjoint from `A`, of `L A B`. -/
noncomputable def V (n : ℕ) : ℝ :=
  ⨆ A : {A : Finset ℝ // AdmissibleMark n A},
    ⨅ B : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B}, L A.1 B.1

/-- The claimed answer value `V(n) = 2^n / (2^(n+1) - 1)`. -/
noncomputable def answer (n : ℕ) : ℝ := (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1)

/-! ## Correctness statements for the definitions

These pin down that the encoded definitions behave as intended. -/

lemma pieceLengths_sum_all (S : Finset ℝ) : (pieceLengths S).sum = 1 := by
  have htel (l : List ℝ) (a b : ℝ) :
      (List.zipWith (fun x y : ℝ => y - x) (a :: (l ++ [b])) (l ++ [b])).sum =
        b - a := by
    induction l generalizing a with
    | nil => simp
    | cons c l ih =>
        simp only [List.cons_append, List.zipWith_cons_cons, List.sum_cons]
        rw [ih]
        ring
  change (List.zipWith (fun x y : ℝ => y - x)
    ((0 : ℝ) :: (S.sort (· ≤ ·) ++ [1])) (S.sort (· ≤ ·) ++ [1])).sum = 1
  rw [htel]
  norm_num

lemma pieceLengths_pos (S : Finset ℝ) (hS : ↑S ⊆ Set.Ioo (0 : ℝ) 1) :
    ∀ z ∈ pieceLengths S, 0 < z := by
  have hsorted : List.Pairwise (· < ·)
      ((0 : ℝ) :: (S.sort (· ≤ ·) ++ [1])) := by
    rw [List.pairwise_cons, List.pairwise_append]
    constructor
    · intro z hz
      simp only [List.mem_append] at hz
      rcases hz with hz | hz
      · have hzS : z ∈ S := by simpa using hz
        exact (hS hzS).1
      · simp at hz
        subst z
        norm_num
    · refine ⟨List.sortedLT_iff_pairwise.mp (Finset.sortedLT_sort S), by simp, ?_⟩
      intro z hz w hw
      simp only [List.mem_singleton] at hw
      subst w
      have hzS : z ∈ S := by simpa using hz
      exact (hS hzS).2
  have hzip : ∀ (l : List ℝ), List.Pairwise (· < ·) l →
      ∀ z ∈ List.zipWith (fun a b : ℝ => b - a) l l.tail, 0 < z := by
    intro l hl
    induction l with
    | nil => simp
    | cons a l ih =>
        cases l with
        | nil => simp
        | cons b l =>
            have hp := List.pairwise_cons.mp hl
            simp only [List.tail_cons, List.zipWith_cons_cons, List.mem_cons]
            intro z hz
            rcases hz with rfl | hz
            · have hab := hp.1 b (by simp)
              linarith
            · exact ih hp.2 z hz
  exact hzip _ hsorted

/-- The piece lengths of an admissible cut set sum to `1` (the total stick
length). -/
theorem pieceLengths_sum (S : Finset ℝ) (hS : ↑S ⊆ Set.Ioo (0 : ℝ) 1) :
    (pieceLengths S).sum = 1 := by
  have _hS := hS
  exact pieceLengths_sum_all S

/-- There are `|S| + 1` pieces. -/
theorem pieceLengths_length (S : Finset ℝ) :
    (pieceLengths S).length = S.card + 1 := by
  simp [pieceLengths, List.length_zipWith]

lemma pieceLengths_nonneg (S : Finset ℝ) (hS : ↑S ⊆ Set.Ioo (0 : ℝ) 1) :
    ∀ z ∈ pieceLengths S, 0 ≤ z := by
  exact fun z hz => (pieceLengths_pos S hS z hz).le

lemma firstPlayerShare_mem_Icc (l : List ℝ) (hn : ∀ z ∈ l, 0 ≤ z) :
    firstPlayerShare l ∈ Set.Icc (0 : ℝ) l.sum := by
  let sorted := l.mergeSort (· ≥ ·)
  let chosen :=
    ((sorted.zipIdx.filter (fun p => p.2 % 2 = 0)).map (fun p => p.1))
  have hsorted_nonneg : ∀ z ∈ sorted, 0 ≤ z := by
    intro z hz
    exact hn z (List.mem_mergeSort.mp hz)
  have hsub : chosen.Sublist sorted := by
    have h := (List.filter_sublist (l := sorted.zipIdx)
      (p := fun p => p.2 % 2 = 0)).map (fun p => p.1)
    simpa [chosen] using h
  have hlo : 0 ≤ chosen.sum := List.sum_nonneg fun z hz => hsorted_nonneg z (hsub.mem hz)
  have hhi : chosen.sum ≤ sorted.sum := hsub.sum_le_sum hsorted_nonneg
  have hsum : sorted.sum = l.sum := (List.mergeSort_perm l (· ≥ ·)).sum_eq
  simpa [firstPlayerShare, sorted, chosen, hsum] using And.intro hlo hhi

/-- Basic sanity bound: Liu Bang's share lies in `[0, 1]` for admissible cut
sets (it is a subset-sum of the piece lengths, which are nonnegative and sum to
`1`). -/
theorem L_mem_Icc (A B : Finset ℝ)
    (hA : ↑A ⊆ Set.Ioo (0 : ℝ) 1) (hB : ↑B ⊆ Set.Ioo (0 : ℝ) 1) :
    L A B ∈ Set.Icc (0 : ℝ) 1 := by
  have hU : ↑(A ∪ B) ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro z hz
    rw [Finset.mem_coe, Finset.mem_union] at hz
    exact hz.elim (fun ha => hA ha) (fun hb => hB hb)
  have hs := firstPlayerShare_mem_Icc (pieceLengths (A ∪ B))
    (pieceLengths_nonneg (A ∪ B) hU)
  rw [pieceLengths_sum (A ∪ B) hU] at hs
  exact hs

lemma admissibleMark_empty (n : ℕ) : AdmissibleMark n ∅ := by
  constructor <;> simp

lemma V_eq_of_bounds (n : ℕ)
    (hlo : ∃ A : Finset ℝ, AdmissibleMark n A ∧
      ∀ B : Finset ℝ, AdmissibleMark n B → Disjoint A B → answer n ≤ L A B)
    (hup : ∀ A : Finset ℝ, AdmissibleMark n A →
      ∃ B : Finset ℝ, AdmissibleMark n B ∧ Disjoint A B ∧ L A B ≤ answer n) :
    V n = answer n := by
  let A0 : {A : Finset ℝ // AdmissibleMark n A} := ⟨∅, admissibleMark_empty n⟩
  letI : Nonempty {A : Finset ℝ // AdmissibleMark n A} := ⟨A0⟩
  let inner : {A : Finset ℝ // AdmissibleMark n A} → ℝ := fun A =>
    ⨅ B : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B}, L A.1 B.1
  have hbddBelow (A : {A : Finset ℝ // AdmissibleMark n A}) :
      BddBelow (Set.range fun B :
        {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B} => L A.1 B.1) := by
    refine ⟨0, ?_⟩
    rintro z ⟨B, rfl⟩
    exact (L_mem_Icc A.1 B.1 A.2.1 B.2.1.1).1
  have hbddAboveOuter : BddAbove (Set.range inner) := by
    refine ⟨1, ?_⟩
    rintro z ⟨A, rfl⟩
    let B0 : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B} :=
      ⟨∅, admissibleMark_empty n, Finset.disjoint_empty_right A.1⟩
    have hi : inner A ≤ L A.1 B0.1 := by
      exact ciInf_le (hbddBelow A) B0
    exact hi.trans (L_mem_Icc A.1 B0.1 A.2.1 B0.2.1.1).2
  apply le_antisymm
  · rw [V]
    apply ciSup_le
    intro A
    rcases hup A.1 A.2 with ⟨B, hB, hd, hL⟩
    let Bs : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B} := ⟨B, hB, hd⟩
    exact ciInf_le_of_le (hbddBelow A) Bs hL
  · rcases hlo with ⟨A, hA, hguar⟩
    let As : {A : Finset ℝ // AdmissibleMark n A} := ⟨A, hA⟩
    let B0 : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint As.1 B} :=
      ⟨∅, admissibleMark_empty n, Finset.disjoint_empty_right As.1⟩
    letI : Nonempty {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint As.1 B} := ⟨B0⟩
    have hi : answer n ≤ inner As := by
      apply le_ciInf
      intro B
      exact hguar B.1 B.2.1 B.2.2
    rw [V]
    exact le_ciSup_of_le hbddAboveOuter As hi

def labelTotal {α : Type*} [DecidableEq α] (a : α) : List ℝ → List α → ℝ
  | x :: xs, b :: bs => (if b = a then x else 0) + labelTotal a xs bs
  | _, _ => 0

namespace P3Realization

def internalCutsFrom (s : ℝ) : List ℝ → List ℝ
  | [] => []
  | [_] => []
  | x :: y :: t => (s + x) :: internalCutsFrom (s + x) (y :: t)

inductive Refines : List ℝ → List ℝ → Prop
  | nil : Refines [] []
  | cons {x : ℝ} {xs ys : List ℝ} (u : List ℝ) (hu : u ≠ [])
      (hsum : u.sum = x) (hrest : Refines xs ys) : Refines (x :: xs) (u ++ ys)

noncomputable def bisectPieces (l : List ℝ) : List ℝ :=
  l.flatMap fun x => [x / 2, x / 2]

lemma refines_bisectPieces (l : List ℝ) : Refines l (bisectPieces l) := by
  induction l with
  | nil => exact Refines.nil
  | cons x xs ih =>
      rw [bisectPieces, List.flatMap_cons]
      exact Refines.cons [x / 2, x / 2] (by simp) (by simp) ih

lemma bisectPieces_length (l : List ℝ) : (bisectPieces l).length = 2 * l.length := by
  induction l with
  | nil => simp [bisectPieces]
  | cons x xs ih => simp [bisectPieces]; omega

lemma bisectPieces_sum (l : List ℝ) : (bisectPieces l).sum = l.sum := by
  induction l with
  | nil => simp [bisectPieces]
  | cons x xs ih =>
      change (List.flatMap (fun y : ℝ => [y / 2, y / 2]) (x :: xs)).sum =
        (x :: xs).sum
      rw [List.flatMap_cons]
      simp only [List.sum_append, List.sum_cons, List.sum_nil, add_zero]
      change (List.flatMap (fun y : ℝ => [y / 2, y / 2]) xs).sum = xs.sum at ih
      rw [ih]
      ring

lemma bisectPieces_pos {l : List ℝ} (hpos : ∀ x ∈ l, 0 < x) :
    ∀ x ∈ bisectPieces l, 0 < x := by
  intro x hx
  simp only [bisectPieces, List.mem_flatMap] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  have hxy' : x = y / 2 := by simpa using hxy
  rw [hxy']
  have hypos := hpos y hy
  linarith

lemma Refines.fine_ne_nil {x : ℝ} {xs ys : List ℝ}
    (h : Refines (x :: xs) ys) : ys ≠ [] := by
  cases h with
  | cons u hu hsum hrest =>
      intro hnil
      exact hu (List.append_eq_nil_iff.mp hnil).1

lemma Refines.sum_eq {xs ys : List ℝ} (h : Refines xs ys) : ys.sum = xs.sum := by
  induction h with
  | nil => simp
  | cons u hu hsum hrest ih => simp [hsum, ih]

lemma internalCutsFrom_append (s : ℝ) (u v : List ℝ)
    (hu : u ≠ []) (hv : v ≠ []) :
    internalCutsFrom s (u ++ v) =
      internalCutsFrom s u ++ (s + u.sum) :: internalCutsFrom (s + u.sum) v := by
  induction u generalizing s with
  | nil => exact (hu rfl).elim
  | cons x xs ih =>
      cases xs with
      | nil =>
          cases v with
          | nil => exact (hv rfl).elim
          | cons y ys => simp [internalCutsFrom]
      | cons y ys =>
          simp only [List.cons_append, internalCutsFrom, List.sum_cons]
          have hrec := ih (s + x) (by simp)
          simp only [List.cons_append, List.sum_cons] at hrec
          rw [hrec]
          congr 1
          ring_nf

lemma mem_internalCutsFrom_iff (s z : ℝ) (l : List ℝ) :
    z ∈ internalCutsFrom s l ↔
      ∃ u v : List ℝ, u ≠ [] ∧ v ≠ [] ∧ l = u ++ v ∧ z = s + u.sum := by
  induction l generalizing s with
  | nil => simp [internalCutsFrom]
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp only [internalCutsFrom, List.not_mem_nil, false_iff]
          rintro ⟨u, v, hu, hv, huv, hz⟩
          have hul : u.length ≠ 0 := fun h => hu (List.eq_nil_of_length_eq_zero h)
          have hvl : v.length ≠ 0 := fun h => hv (List.eq_nil_of_length_eq_zero h)
          have hlen := congrArg List.length huv
          simp only [List.length_cons, List.length_nil, List.length_append] at hlen
          omega
      | cons y ys =>
          rw [internalCutsFrom]
          simp only [List.mem_cons]
          constructor
          · intro hz
            rcases hz with rfl | hz
            · exact ⟨[x], y :: ys, by simp, by simp, by simp, by simp⟩
            · rcases (ih (s + x)).mp hz with ⟨u, v, hu, hv, huv, hzsum⟩
              refine ⟨x :: u, v, by simp, hv, ?_, ?_⟩
              · simp [huv]
              · simp only [List.sum_cons]
                rw [hzsum]
                ring
          · rintro ⟨u, v, hu, hv, huv, hzsum⟩
            cases u with
            | nil => exact (hu rfl).elim
            | cons a us =>
                simp only [List.cons_append, List.cons.injEq] at huv
                rcases huv with ⟨rfl, hus⟩
                cases us with
                | nil =>
                    simp only [List.sum_cons, List.sum_nil, add_zero] at hzsum
                    exact Or.inl (by linarith)
                | cons b bs =>
                    apply Or.inr
                    apply (ih (s + x)).mpr
                    refine ⟨b :: bs, v, by simp, hv, hus, ?_⟩
                    simp only [List.sum_cons] at hzsum ⊢
                    linarith

lemma Refines.internalCuts_subset {xs ys : List ℝ} (h : Refines xs ys) (s : ℝ) :
    ∀ z ∈ internalCutsFrom s xs, z ∈ internalCutsFrom s ys := by
  induction h generalizing s with
  | nil => simp [internalCutsFrom]
  | @cons x xs ys u hu hsum hrest ih =>
      cases xs with
      | nil =>
          cases hrest
          simp [internalCutsFrom]
      | cons y t =>
          have hys : ys ≠ [] := hrest.fine_ne_nil
          rw [internalCutsFrom, internalCutsFrom_append s u ys hu hys]
          intro z hz
          simp only [List.mem_cons] at hz
          rcases hz with rfl | hz
          · simp [hsum]
          · have hz' := ih (s + x) z hz
            rw [hsum]
            simp [hz']

lemma internalCutsFrom_length (s : ℝ) (l : List ℝ) :
    (internalCutsFrom s l).length = l.length - 1 := by
  induction l using List.twoStepInduction generalizing s with
  | nil => simp [internalCutsFrom]
  | singleton x => simp [internalCutsFrom]
  | cons_cons x y t ih ihTail =>
      simp only [internalCutsFrom, List.length_cons]
      have ht := ihTail y (s + x)
      simp at ht ⊢
      exact ht

lemma endpoints_zipWith (s : ℝ) (l : List ℝ) (hl : l ≠ []) :
    List.zipWith (fun a b : ℝ => b - a)
      (s :: (internalCutsFrom s l ++ [s + l.sum]))
      (internalCutsFrom s l ++ [s + l.sum]) = l := by
  induction l using List.twoStepInduction generalizing s with
  | nil => simp at hl
  | singleton x => simp [internalCutsFrom]
  | cons_cons x y t ih ihTail =>
      simp only [internalCutsFrom, List.sum_cons, List.cons_append,
        List.zipWith_cons_cons]
      have htail : y :: t ≠ [] := by simp
      have hrec := ihTail y (s + x) htail
      simp only [List.sum_cons] at hrec
      rw [show s + (x + (y + t.sum)) = s + x + (y + t.sum) by ring]
      rw [hrec]
      congr 1
      ring

lemma internalCutsFrom_zipWith (s e : ℝ) (cuts : List ℝ) :
    internalCutsFrom s
      (List.zipWith (fun a b : ℝ => b - a)
        (s :: (cuts ++ [e])) (cuts ++ [e])) = cuts := by
  induction cuts generalizing s with
  | nil => simp [internalCutsFrom]
  | cons x xs ih =>
      cases xs with
      | nil => simp [internalCutsFrom]
      | cons y ys =>
          simp only [List.cons_append, List.zipWith_cons_cons]
          rw [internalCutsFrom]
          have hsx : s + (x - s) = x := by ring
          rw [hsx]
          congr 1
          exact ih x

lemma internalCutsFrom_gt_start (s : ℝ) (l : List ℝ)
    (hpos : ∀ x ∈ l, 0 < x) :
    ∀ z ∈ internalCutsFrom s l, s < z := by
  induction l using List.twoStepInduction generalizing s with
  | nil => simp [internalCutsFrom]
  | singleton x => simp [internalCutsFrom]
  | cons_cons x y t ih ihTail =>
      simp only [internalCutsFrom, List.mem_cons]
      intro z hz
      rcases hz with rfl | hz
      · have hx := hpos x (by simp)
        linarith
      · have hx := hpos x (by simp)
        have htailpos : ∀ u ∈ y :: t, 0 < u := by
          intro u hu
          exact hpos u (by simp [hu])
        have := ihTail y (s + x) htailpos z hz
        linarith

lemma internalCutsFrom_pairwise (s : ℝ) (l : List ℝ)
    (hpos : ∀ x ∈ l, 0 < x) :
    (internalCutsFrom s l).Pairwise (· < ·) := by
  induction l using List.twoStepInduction generalizing s with
  | nil => simp [internalCutsFrom]
  | singleton x => simp [internalCutsFrom]
  | cons_cons x y t ih ihTail =>
      rw [internalCutsFrom, List.pairwise_cons]
      have htailpos : ∀ u ∈ y :: t, 0 < u := by
        intro u hu
        exact hpos u (by simp [hu])
      constructor
      · intro z hz
        exact internalCutsFrom_gt_start (s + x) (y :: t) htailpos z hz
      · exact ihTail y (s + x) htailpos

lemma internalCutsFrom_lt_end (s : ℝ) (l : List ℝ)
    (hpos : ∀ x ∈ l, 0 < x) :
    ∀ z ∈ internalCutsFrom s l, z < s + l.sum := by
  induction l using List.twoStepInduction generalizing s with
  | nil => simp [internalCutsFrom]
  | singleton x => simp [internalCutsFrom]
  | cons_cons x y t ih ihTail =>
      simp only [internalCutsFrom, List.mem_cons, List.sum_cons]
      intro z hz
      have hy : 0 < y := hpos y (by simp)
      have ht_nonneg : 0 ≤ t.sum := List.sum_nonneg fun u hu =>
        (hpos u (by simp [hu])).le
      rcases hz with rfl | hz
      · linarith
      · have htailpos : ∀ u ∈ y :: t, 0 < u := by
          intro u hu
          exact hpos u (by simp [hu])
        have hrec := ihTail y (s + x) htailpos z hz
        simpa [add_assoc] using hrec

lemma sum_pos_of_pos_of_ne_nil (l : List ℝ) (hne : l ≠ [])
    (hpos : ∀ x ∈ l, 0 < x) : 0 < l.sum := by
  cases l with
  | nil => exact (hne rfl).elim
  | cons x xs =>
      have hx := hpos x (by simp)
      have htail : 0 ≤ xs.sum := List.sum_nonneg fun z hz => (hpos z (by simp [hz])).le
      simp only [List.sum_cons]
      linarith

lemma refines_of_internalCuts_subset (s : ℝ) {xs ys : List ℝ}
    (hxpos : ∀ x ∈ xs, 0 < x) (hypos : ∀ y ∈ ys, 0 < y)
    (hsum : ys.sum = xs.sum)
    (hsub : ∀ z ∈ internalCutsFrom s xs, z ∈ internalCutsFrom s ys) :
    Refines xs ys := by
  induction xs generalizing s ys with
  | nil =>
      have hys : ys = [] := by
        by_contra hne
        have hp := sum_pos_of_pos_of_ne_nil ys hne hypos
        simp only [List.sum_nil] at hsum
        linarith
      subst ys
      exact Refines.nil
  | cons x xs ih =>
      cases xs with
      | nil =>
          have hx : 0 < x := hxpos x (by simp)
          have hys : ys ≠ [] := by
            intro heq
            subst ys
            simp at hsum
            linarith
          simpa using Refines.cons ys hys (by simpa using hsum) Refines.nil
      | cons y t =>
          have hboundary : s + x ∈ internalCutsFrom s (x :: y :: t) := by
            simp [internalCutsFrom]
          have hboundaryFine := hsub (s + x) hboundary
          rcases (mem_internalCutsFrom_iff s (s + x) ys).mp hboundaryFine with
            ⟨u, v, hu, hv, huv, hubound⟩
          have husum : u.sum = x := by linarith
          have hupos : ∀ z ∈ u, 0 < z := by
            intro z hz
            exact hypos z (huv ▸ List.mem_append_left v hz)
          have hvpos : ∀ z ∈ v, 0 < z := by
            intro z hz
            exact hypos z (huv ▸ List.mem_append_right u hz)
          have htailsum : v.sum = (y :: t).sum := by
            rw [huv, List.sum_append, husum] at hsum
            simp only [List.sum_cons] at hsum ⊢
            linarith
          have htailSub : ∀ z ∈ internalCutsFrom (s + x) (y :: t),
              z ∈ internalCutsFrom (s + x) v := by
            intro z hz
            have hzgt := internalCutsFrom_gt_start (s + x) (y :: t)
              (fun w hw => hxpos w (by simp [hw])) z hz
            have hzCoarse : z ∈ internalCutsFrom s (x :: y :: t) := by
              simp [internalCutsFrom, hz]
            have hzFine := hsub z hzCoarse
            rw [huv, internalCutsFrom_append s u v hu hv] at hzFine
            simp only [List.mem_append, List.mem_cons] at hzFine
            rcases hzFine with hzU | rfl | hzV
            · have hzlt := internalCutsFrom_lt_end s u hupos z hzU
              rw [husum] at hzlt
              linarith
            · linarith
            · rwa [husum] at hzV
          have hrest : Refines (y :: t) v := by
            apply ih (s + x) (ys := v)
            · intro w hw
              exact hxpos w (by simp [hw])
            · exact hvpos
            · exact htailsum
            · exact htailSub
          rw [huv]
          exact Refines.cons u hu husum hrest

noncomputable def cutFinset (l : List ℝ) : Finset ℝ :=
  (internalCutsFrom 0 l).toFinset

lemma cutFinset_card (l : List ℝ) (hpos : ∀ x ∈ l, 0 < x) :
    (cutFinset l).card = l.length - 1 := by
  rw [cutFinset, List.card_toFinset,
    List.dedup_eq_self.mpr (internalCutsFrom_pairwise 0 l hpos).nodup]
  exact internalCutsFrom_length 0 l

lemma cutFinset_admissible (l : List ℝ) (hpos : ∀ x ∈ l, 0 < x)
    (hsum : l.sum = 1) :
    ↑(cutFinset l) ⊆ Set.Ioo (0 : ℝ) 1 := by
  intro z hz
  rw [Finset.mem_coe, cutFinset, List.mem_toFinset] at hz
  constructor
  · exact internalCutsFrom_gt_start 0 l hpos z hz
  · have := internalCutsFrom_lt_end 0 l hpos z hz
    simpa [hsum] using this

lemma pieceLengths_cutFinset (l : List ℝ) (hne : l ≠ [])
    (hpos : ∀ x ∈ l, 0 < x) (hsum : l.sum = 1) :
    pieceLengths (cutFinset l) = l := by
  have hpairlt := internalCutsFrom_pairwise 0 l hpos
  have hnodup := hpairlt.nodup
  have hpairle : (internalCutsFrom 0 l).Pairwise (· ≤ ·) :=
    hpairlt.imp fun h => le_of_lt h
  have hsort : (cutFinset l).sort (· ≤ ·) = internalCutsFrom 0 l := by
    rw [cutFinset]
    exact (List.toFinset_sort (· ≤ ·) hnodup).2 hpairle
  rw [pieceLengths, hsort]
  change List.zipWith (fun a b : ℝ => b - a)
      ((0 : ℝ) :: (internalCutsFrom 0 l ++ [1]))
      (internalCutsFrom 0 l ++ [1]) = l
  convert endpoints_zipWith 0 l hne using 1
  all_goals simp [hsum]

lemma cutFinset_pieceLengths (S : Finset ℝ) :
    cutFinset (pieceLengths S) = S := by
  rw [cutFinset]
  change (internalCutsFrom 0
    (List.zipWith (fun a b : ℝ => b - a)
      ((0 : ℝ) :: (S.sort (· ≤ ·) ++ [1])) (S.sort (· ≤ ·) ++ [1]))).toFinset = S
  rw [internalCutsFrom_zipWith]
  exact Finset.sort_toFinset S (· ≤ ·)

lemma Refines.cutFinset_subset {xs ys : List ℝ} (h : Refines xs ys) :
    cutFinset xs ⊆ cutFinset ys := by
  intro z hz
  rw [cutFinset, List.mem_toFinset] at hz ⊢
  exact h.internalCuts_subset 0 z hz

lemma pieceLengths_refines_of_subset {S T : Finset ℝ}
    (hS : ↑S ⊆ Set.Ioo (0 : ℝ) 1) (hT : ↑T ⊆ Set.Ioo (0 : ℝ) 1)
    (hST : S ⊆ T) : Refines (pieceLengths S) (pieceLengths T) := by
  apply refines_of_internalCuts_subset 0
  · exact pieceLengths_pos S hS
  · exact pieceLengths_pos T hT
  · rw [pieceLengths_sum_all, pieceLengths_sum_all]
  · intro z hz
    have hzS : z ∈ cutFinset (pieceLengths S) := by
      simpa [cutFinset] using hz
    have hzT : z ∈ cutFinset (pieceLengths T) := by
      rw [cutFinset_pieceLengths] at hzS ⊢
      exact hST hzS
    simpa [cutFinset] using hzT

lemma labelTotal_append {α : Type*} [DecidableEq α] (a : α)
    (xs ys : List ℝ) (ls ms : List α) (hlen : xs.length = ls.length) :
    labelTotal a (xs ++ ys) (ls ++ ms) =
      labelTotal a xs ls + labelTotal a ys ms := by
  induction xs generalizing ls with
  | nil =>
      have : ls = [] := List.eq_nil_of_length_eq_zero hlen.symm
      subst ls
      simp [labelTotal]
  | cons x xs ih =>
      cases ls with
      | nil => simp at hlen
      | cons b bs =>
          simp only [List.cons_append, labelTotal]
          rw [ih bs (by simpa using hlen)]
          ring

lemma labelTotal_replicate_same {α : Type*} [DecidableEq α]
    (a : α) (xs : List ℝ) :
    labelTotal a xs (List.replicate xs.length a) = xs.sum := by
  induction xs with
  | nil => simp [labelTotal]
  | cons x xs ih =>
      simpa [List.replicate_succ, labelTotal] using congrArg (fun z => x + z) ih

lemma labelTotal_replicate_ne {α : Type*} [DecidableEq α]
    {a b : α} (hab : b ≠ a) (xs : List ℝ) :
    labelTotal a xs (List.replicate xs.length b) = 0 := by
  induction xs with
  | nil => simp [labelTotal]
  | cons x xs ih =>
      simpa [List.replicate_succ, labelTotal, hab] using ih

lemma labelTotal_map_succ_zero {n : ℕ} (xs : List ℝ) (ls : List (Fin n)) :
    labelTotal (0 : Fin (n + 1)) xs (ls.map Fin.succ) = 0 := by
  induction xs generalizing ls with
  | nil => simp [labelTotal]
  | cons x xs ih =>
      cases ls with
      | nil => simp [labelTotal]
      | cons b bs => simp [labelTotal, ih]

lemma labelTotal_map_succ_succ {n : ℕ} (i : Fin n)
    (xs : List ℝ) (ls : List (Fin n)) :
    labelTotal i.succ xs (ls.map Fin.succ) = labelTotal i xs ls := by
  induction xs generalizing ls with
  | nil => simp [labelTotal]
  | cons x xs ih =>
      cases ls with
      | nil => simp [labelTotal]
      | cons b bs =>
          simp only [List.map_cons, labelTotal, Fin.succ_inj]
          rw [ih]

lemma Refines.exists_finLabels {xs ys : List ℝ} (h : Refines xs ys) :
    ∃ labels : List (Fin xs.length),
      labels.length = ys.length ∧
      ∀ i : Fin xs.length, labelTotal i ys labels = xs.get i := by
  induction h with
  | nil =>
      exact ⟨[], by simp, fun i => Fin.elim0 i⟩
  | @cons x xs ys u hu hsum hrest ih =>
      obtain ⟨labels, hlen, htot⟩ := ih
      let labels' : List (Fin (x :: xs).length) :=
        List.replicate u.length 0 ++ labels.map Fin.succ
      refine ⟨labels', ?_, ?_⟩
      · simp [labels', hlen]
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · rw [show (u ++ ys) = u ++ ys by rfl]
          rw [labelTotal_append (0 : Fin (x :: xs).length) u ys
            (List.replicate u.length 0) (labels.map Fin.succ) (by simp)]
          rw [labelTotal_replicate_same, labelTotal_map_succ_zero, hsum]
          simp
        · rw [labelTotal_append j.succ u ys
            (List.replicate u.length 0) (labels.map Fin.succ) (by simp)]
          rw [labelTotal_replicate_ne (a := j.succ) (b := 0) (by
            intro h
            simpa using congrArg Fin.val h), labelTotal_map_succ_succ, htot]
          simp

noncomputable def extraCuts (A : Finset ℝ) (l : List ℝ) : Finset ℝ :=
  cutFinset l \ A

lemma extraCuts_disjoint (A : Finset ℝ) (l : List ℝ) :
    Disjoint A (extraCuts A l) := by
  rw [Finset.disjoint_left]
  intro z hzA hzB
  exact (Finset.mem_sdiff.mp hzB).2 hzA

lemma union_extraCuts {A : Finset ℝ} {l : List ℝ} (hA : A ⊆ cutFinset l) :
    A ∪ extraCuts A l = cutFinset l := by
  ext z
  simp only [extraCuts, Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro (hz | ⟨hz, _⟩)
    · exact hA hz
    · exact hz
  · intro hz
    by_cases hza : z ∈ A
    · exact Or.inl hza
    · exact Or.inr ⟨hz, hza⟩

lemma extraCuts_card {A : Finset ℝ} {l : List ℝ} (hA : A ⊆ cutFinset l)
    (hpos : ∀ x ∈ l, 0 < x) :
    (extraCuts A l).card = l.length - 1 - A.card := by
  rw [extraCuts, Finset.card_sdiff_of_subset hA, cutFinset_card l hpos]

lemma extraCuts_admissible {A : Finset ℝ} {l : List ℝ}
    (hpos : ∀ x ∈ l, 0 < x) (hsum : l.sum = 1) :
    ↑(extraCuts A l) ⊆ Set.Ioo (0 : ℝ) 1 := by
  intro z hz
  apply cutFinset_admissible l hpos hsum
  exact (Finset.mem_sdiff.mp hz).1

end P3Realization

def alternatingShare : List ℝ → ℝ
  | [] => 0
  | a :: [] => a
  | a :: _b :: t => a + alternatingShare t

def alternatingDiscrepancy : List ℝ → ℝ
  | [] => 0
  | a :: [] => a
  | a :: b :: t => (a - b) + alternatingDiscrepancy t

def indexedEvenShare : ℕ → List ℝ → ℝ
  | _, [] => 0
  | k, a :: t => (if k % 2 = 0 then a else 0) + indexedEvenShare (k + 1) t

lemma zipIdx_even_sum_eq_indexedEvenShare (l : List ℝ) (k : ℕ) :
    (((l.zipIdx k).filter (fun p => p.2 % 2 = 0)).map (fun p => p.1)).sum =
      indexedEvenShare k l := by
  induction l generalizing k with
  | nil => simp [indexedEvenShare]
  | cons a t ih =>
      rw [List.zipIdx_cons]
      by_cases hk : k % 2 = 0
      · simp [hk, indexedEvenShare, ih]
      · simp [hk, indexedEvenShare, ih]

lemma indexedEvenShare_add_two (l : List ℝ) (k : ℕ) :
    indexedEvenShare (k + 2) l = indexedEvenShare k l := by
  induction l generalizing k with
  | nil => rfl
  | cons a t ih =>
      simp only [indexedEvenShare]
      rw [show (k + 2) % 2 = k % 2 by omega]
      rw [show k + 2 + 1 = (k + 1) + 2 by omega, ih]

lemma indexedEvenShare_zero_eq_alternatingShare (l : List ℝ) :
    indexedEvenShare 0 l = alternatingShare l := by
  induction l using List.twoStepInduction with
  | nil => rfl
  | singleton a => simp [indexedEvenShare, alternatingShare]
  | cons_cons a b t ih =>
      simp only [indexedEvenShare, alternatingShare]
      rw [indexedEvenShare_add_two t 0, ih]
      norm_num

lemma firstPlayerShare_eq_alternatingShare (l : List ℝ) :
    firstPlayerShare l = alternatingShare (l.mergeSort (· ≥ ·)) := by
  rw [firstPlayerShare, zipIdx_even_sum_eq_indexedEvenShare,
    indexedEvenShare_zero_eq_alternatingShare]

lemma twice_alternatingShare (l : List ℝ) :
    2 * alternatingShare l = l.sum + alternatingDiscrepancy l := by
  induction l using List.twoStepInduction with
  | nil => simp [alternatingShare, alternatingDiscrepancy]
  | singleton a => simp [alternatingShare, alternatingDiscrepancy]; ring
  | cons_cons a b t ih =>
      simp only [alternatingShare, alternatingDiscrepancy, List.sum_cons]
      linarith

def PairOpposite {α : Type*} (σ : α → ℝ) : List α → Prop
  | [] => True
  | [_] => True
  | a :: b :: t => σ a = -σ b ∧ PairOpposite σ t

def weightedByLabel {α : Type*} (σ : α → ℝ) : List ℝ → List α → ℝ
  | x :: xs, a :: as => σ a * x + weightedByLabel σ xs as
  | _, _ => 0

lemma weightedByLabel_eq_sum_labelTotal
    {α : Type*} [Fintype α] [DecidableEq α]
    (σ : α → ℝ) (xs : List ℝ) (labels : List α)
    (hlen : labels.length = xs.length) :
    weightedByLabel σ xs labels = ∑ a, σ a * labelTotal a xs labels := by
  induction xs generalizing labels with
  | nil =>
      have : labels = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst labels
      simp [weightedByLabel, labelTotal]
  | cons x xs ih =>
      cases labels with
      | nil => simp at hlen
      | cons b bs =>
        have hlen' : bs.length = xs.length := by simpa using hlen
        simp only [weightedByLabel, labelTotal, mul_add, Finset.sum_add_distrib]
        rw [← ih bs hlen']
        simp

lemma abs_weightedByLabel_le_discrepancy
    {α : Type*} (σ : α → ℝ) (xs : List ℝ) (labels : List α)
    (hlen : labels.length = xs.length)
    (hsort : xs.Pairwise (· ≥ ·))
    (hnonneg : ∀ x ∈ xs, 0 ≤ x)
    (hσ : ∀ a ∈ labels, |σ a| ≤ 1)
    (hop : PairOpposite σ labels) :
    |weightedByLabel σ xs labels| ≤ alternatingDiscrepancy xs := by
  induction xs using List.twoStepInduction generalizing labels with
  | nil =>
      have : labels = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst labels
      simp [weightedByLabel, alternatingDiscrepancy]
  | singleton x =>
      obtain ⟨a, rfl⟩ : ∃ a, labels = [a] := by
        cases labels with
        | nil => simp at hlen
        | cons a ls =>
          cases ls with
          | nil => exact ⟨a, rfl⟩
          | cons b ls => simp at hlen
      have hx : 0 ≤ x := hnonneg x (by simp)
      have ha : |σ a| ≤ 1 := hσ a (by simp)
      have := mul_le_mul_of_nonneg_right ha hx
      simpa [weightedByLabel, alternatingDiscrepancy, abs_mul,
        abs_of_nonneg hx] using this
  | cons_cons x y t ih =>
      obtain ⟨a, b, ls, rfl⟩ : ∃ a b ls, labels = a :: b :: ls := by
        cases labels with
        | nil => simp at hlen
        | cons a labels =>
          cases labels with
          | nil => simp at hlen
          | cons b ls => exact ⟨a, b, ls, rfl⟩
      have hlent : ls.length = t.length := by simpa using hlen
      have hxy : y ≤ x := by
        simpa using (List.pairwise_cons.mp hsort).1 y (by simp)
      have ht : t.Pairwise (· ≥ ·) :=
        (List.pairwise_cons.mp (List.pairwise_cons.mp hsort).2).2
      have htn : ∀ z ∈ t, 0 ≤ z := by
        intro z hz
        exact hnonneg z (by simp [hz])
      have hlsσ : ∀ c ∈ ls, |σ c| ≤ 1 := by
        intro c hc
        exact hσ c (by simp [hc])
      obtain ⟨hab, hopt⟩ := hop
      have iht := ih ls hlent ht htn hlsσ hopt
      have ha : |σ a| ≤ 1 := hσ a (by simp)
      have hpart : |σ a * (x - y)| ≤ x - y := by
        rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hxy)]
        nlinarith [abs_nonneg (σ a)]
      simp only [weightedByLabel, alternatingDiscrepancy]
      rw [hab]
      have hrearrange : -σ b * x + σ b * y = (-σ b) * (x - y) := by ring
      rw [← add_assoc, hrearrange]
      calc
        |(-σ b) * (x - y) + weightedByLabel σ t ls| ≤
            |(-σ b) * (x - y)| + |weightedByLabel σ t ls| := abs_add_le _ _
        _ = |σ a * (x - y)| + |weightedByLabel σ t ls| := by rw [hab]
        _ ≤ (x - y) + alternatingDiscrepancy t := add_le_add hpart iht

def signedBinaryFin : (n : ℕ) → (Fin n → ℤ) → ℤ
  | 0, _ => 0
  | n + 1, ε => ε 0 + 2 * signedBinaryFin n (fun i => ε i.succ)

lemma signedBinaryFin_eq_sum (n : ℕ) (ε : Fin n → ℤ) :
    signedBinaryFin n ε = ∑ i, ε i * (2 : ℤ) ^ (i : ℕ) := by
  induction n with
  | zero => simp [signedBinaryFin]
  | succ n ih =>
      rw [Fin.sum_univ_succ]
      simp only [signedBinaryFin, Fin.val_zero, pow_zero, mul_one]
      rw [ih]
      simp_rw [Fin.val_succ, pow_succ]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring

lemma signedBinaryFin_ne_zero
    (n : ℕ) (ε : Fin n → ℤ)
    (hvals : ∀ i, ε i = -1 ∨ ε i = 0 ∨ ε i = 1)
    (hne : ∃ i, ε i ≠ 0) :
    signedBinaryFin n ε ≠ 0 := by
  induction n with
  | zero =>
      obtain ⟨i, _hi⟩ := hne
      exact Fin.elim0 i
  | succ n ih =>
      let ε' : Fin n → ℤ := fun i => ε i.succ
      by_cases hzero : ε 0 = 0
      · have hne' : ∃ i, ε' i ≠ 0 := by
          by_contra h
          simp only [not_exists, not_not] at h
          obtain ⟨i, hi⟩ := hne
          refine hi ?_
          refine Fin.cases hzero ?_ i
          intro j
          exact h j
        have hvals' : ∀ i, ε' i = -1 ∨ ε' i = 0 ∨ ε' i = 1 := fun i => hvals i.succ
        simp only [signedBinaryFin, hzero, zero_add]
        exact mul_ne_zero (by norm_num) (ih ε' hvals' hne')
      · have hone : ε 0 = -1 ∨ ε 0 = 1 := by
          rcases hvals 0 with h | h | h
          · exact Or.inl h
          · exact (hzero h).elim
          · exact Or.inr h
        simp only [signedBinaryFin]
        rcases hone with hone | hone <;> rw [hone] <;> omega

lemma one_le_abs_signedBinaryFin
    (n : ℕ) (ε : Fin n → ℤ)
    (hvals : ∀ i, ε i = -1 ∨ ε i = 0 ∨ ε i = 1)
    (hne : ∃ i, ε i ≠ 0) :
    (1 : ℝ) ≤ |(signedBinaryFin n ε : ℝ)| := by
  have hz := signedBinaryFin_ne_zero n ε hvals hne
  have hi : (1 : ℤ) ≤ |signedBinaryFin n ε| := Int.one_le_abs hz
  exact_mod_cast hi

lemma cast_signedBinaryFin_eq_sum (n : ℕ) (ε : Fin n → ℤ) :
    (signedBinaryFin n ε : ℝ) =
      ∑ i, (ε i : ℝ) * (2 : ℝ) ^ (i : ℕ) := by
  rw [signedBinaryFin_eq_sum]
  push_cast
  rfl

lemma discrepancy_ge_of_binary_component_certificate
    (n : ℕ) (xs : List ℝ) (labels : List (Fin n)) (δ : ℝ)
    (ε : Fin n → ℤ)
    (hlen : labels.length = xs.length)
    (hsort : xs.Pairwise (· ≥ ·))
    (hnonneg : ∀ x ∈ xs, 0 ≤ x)
    (hgroup : ∀ i, labelTotal i xs labels = δ * (2 : ℝ) ^ (i : ℕ))
    (hδ : 0 < δ)
    (hvals : ∀ i, ε i = -1 ∨ ε i = 0 ∨ ε i = 1)
    (hne : ∃ i, ε i ≠ 0)
    (hop : PairOpposite (fun i => (ε i : ℝ)) labels) :
    δ ≤ alternatingDiscrepancy xs := by
  have hcoeff : ∀ i ∈ labels, |(ε i : ℝ)| ≤ 1 := by
    intro i hi
    rcases hvals i with h | h | h <;> rw [h] <;> norm_num
  have hwle := abs_weightedByLabel_le_discrepancy
    (fun i => (ε i : ℝ)) xs labels hlen hsort hnonneg hcoeff hop
  have hw : weightedByLabel (fun i => (ε i : ℝ)) xs labels =
      δ * (signedBinaryFin n ε : ℝ) := by
    rw [weightedByLabel_eq_sum_labelTotal _ xs labels hlen]
    simp_rw [hgroup]
    rw [cast_signedBinaryFin_eq_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hw, abs_mul, abs_of_pos hδ] at hwle
  have hone := one_le_abs_signedBinaryFin n ε hvals hne
  nlinarith [abs_nonneg (signedBinaryFin n ε : ℝ)]

def pairLabels {α : Type*} : List α → List (α × α)
  | a :: b :: t => (a, b) :: pairLabels t
  | _ => []

lemma pairLabels_length {α : Type*} (l : List α) :
    (pairLabels l).length = l.length / 2 := by
  induction l using List.twoStepInduction with
  | nil => simp [pairLabels]
  | singleton a => simp [pairLabels]
  | cons_cons a b t ih =>
      simp only [pairLabels, List.length_cons]
      rw [ih]
      omega

noncomputable def pairConstraintMap (n : ℕ) (edges : List (Fin n × Fin n)) :
    (Fin n → ZMod 3) →ₗ[ZMod 3] (Fin edges.length → ZMod 3) where
  toFun v i := v (edges.get i).1 + v (edges.get i).2
  map_add' v w := by
    funext i
    simp
    ac_rfl
  map_smul' r v := by
    funext i
    simp [mul_add]

lemma exists_nonzero_pair_kernel
    (n : ℕ) (labels : List (Fin n))
    (hedges : (pairLabels labels).length < n) :
    ∃ v : Fin n → ZMod 3, v ≠ 0 ∧
      ∀ e ∈ pairLabels labels, v e.1 + v e.2 = 0 := by
  let edges := pairLabels labels
  let T := pairConstraintMap n edges
  have hdim : Module.finrank (ZMod 3) (Fin edges.length → ZMod 3) <
      Module.finrank (ZMod 3) (Fin n → ZMod 3) := by
    simpa using hedges
  have hker : LinearMap.ker T ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨v, hvker, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨v, hvne, ?_⟩
  intro e he
  obtain ⟨i, hi⟩ := List.get_of_mem (show e ∈ edges by simpa [edges] using he)
  have hmap : T v = 0 := LinearMap.mem_ker.mp hvker
  have hcoord := congrFun hmap i
  change v (edges.get i).1 + v (edges.get i).2 = 0 at hcoord
  rw [hi] at hcoord
  exact hcoord

def zmod3Sign (z : ZMod 3) : ℤ :=
  if z = 0 then 0 else if z = 1 then 1 else -1

lemma zmod3Sign_values (z : ZMod 3) :
    zmod3Sign z = -1 ∨ zmod3Sign z = 0 ∨ zmod3Sign z = 1 := by
  simp only [zmod3Sign]
  split_ifs <;> simp

lemma zmod3Sign_eq_zero_iff (z : ZMod 3) : zmod3Sign z = 0 ↔ z = 0 := by
  constructor
  · intro h
    simp only [zmod3Sign] at h
    split at h
    · assumption
    · split at h <;> norm_num at h
  · intro h
    subst z
    simp [zmod3Sign]

lemma zmod3Sign_neg (z : ZMod 3) : zmod3Sign (-z) = -zmod3Sign z := by
  fin_cases z <;> decide

lemma pairOpposite_of_pair_kernel
    {n : ℕ} (labels : List (Fin n)) (v : Fin n → ZMod 3)
    (hv : ∀ e ∈ pairLabels labels, v e.1 + v e.2 = 0) :
    PairOpposite (fun i => (zmod3Sign (v i) : ℝ)) labels := by
  induction labels using List.twoStepInduction with
  | nil => trivial
  | singleton a => trivial
  | cons_cons a b t ih =>
      have hab : v a + v b = 0 := hv (a, b) (by simp [pairLabels])
      have hab' : v a = -v b := eq_neg_of_add_eq_zero_left hab
      have hsign := congrArg zmod3Sign hab'
      rw [zmod3Sign_neg] at hsign
      constructor
      · change (zmod3Sign (v a) : ℝ) = -(zmod3Sign (v b) : ℝ)
        exact_mod_cast hsign
      · apply ih
        intro e he
        exact hv e (by simp [pairLabels, he])

lemma exists_binary_pair_certificate
    (n : ℕ) (labels : List (Fin n))
    (hedges : labels.length / 2 < n) :
    ∃ ε : Fin n → ℤ,
      (∀ i, ε i = -1 ∨ ε i = 0 ∨ ε i = 1) ∧
      (∃ i, ε i ≠ 0) ∧
      PairOpposite (fun i => (ε i : ℝ)) labels := by
  have hedge' : (pairLabels labels).length < n := by
    rwa [pairLabels_length]
  obtain ⟨v, hvne, hv⟩ := exists_nonzero_pair_kernel n labels hedge'
  let ε : Fin n → ℤ := fun i => zmod3Sign (v i)
  refine ⟨ε, fun i => zmod3Sign_values (v i), ?_, ?_⟩
  · by_contra h
    simp only [not_exists, not_not] at h
    apply hvne
    funext i
    exact (zmod3Sign_eq_zero_iff (v i)).mp (h i)
  · exact pairOpposite_of_pair_kernel labels v hv

lemma discrepancy_ge_binary_partition
    (N : ℕ) (xs : List ℝ) (labels : List (Fin N)) (δ : ℝ)
    (hN : 0 < N)
    (hlen : labels.length = xs.length)
    (hcard : xs.length ≤ 2 * N - 1)
    (hsort : xs.Pairwise (· ≥ ·))
    (hnonneg : ∀ x ∈ xs, 0 ≤ x)
    (hgroup : ∀ i, labelTotal i xs labels = δ * (2 : ℝ) ^ (i : ℕ))
    (hδ : 0 < δ) :
    δ ≤ alternatingDiscrepancy xs := by
  have hedge : labels.length / 2 < N := by
    rw [hlen]
    omega
  obtain ⟨ε, hvals, hne, hop⟩ := exists_binary_pair_certificate N labels hedge
  exact discrepancy_ge_of_binary_component_certificate
    N xs labels δ ε hlen hsort hnonneg hgroup hδ hvals hne hop

lemma alternatingShare_ge_top_binary_gap
    (n : ℕ) (xs : List ℝ) (labels : List (Fin (n + 1))) (δ : ℝ)
    (hlen : labels.length = xs.length)
    (hcard : xs.length ≤ 2 * (n + 1) - 1)
    (hsort : xs.Pairwise (· ≥ ·))
    (hnonneg : ∀ x ∈ xs, 0 ≤ x)
    (hsum : xs.sum = δ * ((2 : ℝ) ^ (n + 1) - 1))
    (hgroup : ∀ i, labelTotal i xs labels = δ * (2 : ℝ) ^ (i : ℕ))
    (hδ : 0 < δ) :
    δ * (2 : ℝ) ^ n ≤ alternatingShare xs := by
  have hd := discrepancy_ge_binary_partition (n + 1) xs labels δ
    (by omega) hlen hcard hsort hnonneg hgroup hδ
  have htwice := twice_alternatingShare xs
  have hpow : (2 : ℝ) ^ (n + 1) = 2 * (2 : ℝ) ^ n := by
    rw [pow_succ]
    ring
  rw [hsum, hpow] at htwice
  nlinarith

lemma permute_labels_preserves_totals
    {α : Type*} [Fintype α] [DecidableEq α]
    {xs ys : List ℝ} (hperm : xs.Perm ys) (labels : List α)
    (hlen : labels.length = xs.length) :
    ∃ labels' : List α, labels'.length = ys.length ∧
      ∀ a, labelTotal a ys labels' = labelTotal a xs labels := by
  induction hperm generalizing labels with
  | nil =>
      have : labels = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      subst labels
      exact ⟨[], rfl, by simp [labelTotal]⟩
  | cons x hperm ih =>
      cases labels with
      | nil => simp at hlen
      | cons a labels =>
        obtain ⟨labels', hlen', htot⟩ := ih labels (by simpa using hlen)
        refine ⟨a :: labels', by simp [hlen'], ?_⟩
        intro b
        simp only [labelTotal]
        rw [htot]
  | swap x y t =>
      cases labels with
      | nil => simp at hlen
      | cons a labels =>
        cases labels with
        | nil => simp at hlen
        | cons b labels =>
          refine ⟨b :: a :: labels, by simpa using hlen, ?_⟩
          intro c
          simp only [labelTotal]
          split_ifs <;> ring
  | trans hxy hyz ihxy ihyz =>
      obtain ⟨labels', hlen', htot'⟩ := ihxy labels hlen
      obtain ⟨labels'', hlen'', htot''⟩ := ihyz labels' hlen'
      refine ⟨labels'', hlen'', ?_⟩
      intro a
      rw [htot'', htot']

noncomputable def binaryDelta (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ (n + 1) - 1)

noncomputable def binaryGaps (n : ℕ) : List ℝ :=
  List.ofFn (fun i : Fin (n + 1) => binaryDelta n * (2 : ℝ) ^ (i : ℕ))

lemma binaryDelta_pos (n : ℕ) : 0 < binaryDelta n := by
  unfold binaryDelta
  apply one_div_pos.mpr
  have hp : (1 : ℝ) < (2 : ℝ) ^ (n + 1) :=
    pow_lt_pow_right₀ (a := (2 : ℝ)) (m := 0) (n := n + 1) (by norm_num) (by omega)
  linarith

lemma binaryGaps_pos (n : ℕ) : ∀ x ∈ binaryGaps n, 0 < x := by
  intro x hx
  have hx' : x ∈ List.ofFn
      (fun i : Fin (n + 1) => binaryDelta n * (2 : ℝ) ^ (i : ℕ)) := by
    simpa only [binaryGaps] using hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx'
  exact mul_pos (binaryDelta_pos n) (by positivity)

lemma binaryGaps_length (n : ℕ) : (binaryGaps n).length = n + 1 := by
  simp [binaryGaps]

lemma binaryGaps_sum (n : ℕ) : (binaryGaps n).sum = 1 := by
  rw [binaryGaps, List.sum_ofFn]
  rw [← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range, geom_sum_eq]
  · rw [binaryDelta]
    have hp : (1 : ℝ) < (2 : ℝ) ^ (n + 1) :=
      pow_lt_pow_right₀ (a := (2 : ℝ)) (m := 0) (n := n + 1) (by norm_num) (by omega)
    have hden : (2 : ℝ) ^ (n + 1) - 1 ≠ 0 := by linarith
    field_simp [hden]
    norm_num
  · norm_num

lemma binaryDelta_mul_geom (n : ℕ) :
    binaryDelta n * ((2 : ℝ) ^ (n + 1) - 1) = 1 := by
  have hp : (1 : ℝ) < (2 : ℝ) ^ (n + 1) :=
    pow_lt_pow_right₀ (a := (2 : ℝ)) (m := 0) (n := n + 1) (by norm_num) (by omega)
  have hden : (2 : ℝ) ^ (n + 1) - 1 ≠ 0 := by linarith
  rw [binaryDelta]
  field_simp [hden]

lemma labelTotal_map_equiv
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (a : α) (xs : List ℝ) (labels : List α) :
    labelTotal (e a) xs (labels.map e) = labelTotal a xs labels := by
  induction xs generalizing labels with
  | nil => simp [labelTotal]
  | cons x xs ih =>
      cases labels with
      | nil => simp [labelTotal]
      | cons b labels =>
          simp only [List.map_cons, labelTotal, e.injective.eq_iff]
          rw [ih]

theorem lower_bound_aux (n : ℕ) (hn : 0 < n) :
    ∃ A : Finset ℝ, AdmissibleMark n A ∧
      ∀ B : Finset ℝ, AdmissibleMark n B → Disjoint A B →
        (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1) ≤ L A B := by
  let A : Finset ℝ := P3Realization.cutFinset (binaryGaps n)
  have hgapPos := binaryGaps_pos n
  have hgapSum := binaryGaps_sum n
  have hAint : ↑A ⊆ Set.Ioo (0 : ℝ) 1 := by
    dsimp [A]
    exact P3Realization.cutFinset_admissible (binaryGaps n) hgapPos hgapSum
  have hAcard : A.card = n := by
    dsimp [A]
    rw [P3Realization.cutFinset_card (binaryGaps n) hgapPos,
      binaryGaps_length]
    omega
  refine ⟨A, ⟨hAint, hAcard.le⟩, ?_⟩
  intro B hB _hdisjoint
  let T : Finset ℝ := A ∪ B
  have hTint : ↑T ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro x hx
    change x ∈ T at hx
    change x ∈ A ∪ B at hx
    rw [Finset.mem_union] at hx
    rcases hx with hx | hx
    · exact hAint hx
    · exact hB.1 hx
  have hcoarse : pieceLengths A = binaryGaps n := by
    dsimp [A]
    apply P3Realization.pieceLengths_cutFinset
    · intro hnil
      have hlen := binaryGaps_length n
      rw [hnil] at hlen
      simp at hlen
    · exact hgapPos
    · exact hgapSum
  have hrefine : P3Realization.Refines (binaryGaps n) (pieceLengths T) := by
    rw [← hcoarse]
    exact P3Realization.pieceLengths_refines_of_subset hAint hTint
      (by exact Finset.subset_union_left)
  obtain ⟨labels, hlabelsLen, hlabelsTotal⟩ :=
    P3Realization.Refines.exists_finLabels hrefine
  let labelEquiv : Fin (binaryGaps n).length ≃ Fin (n + 1) :=
    (Fin.castOrderIso (binaryGaps_length n)).toEquiv
  let labelsN : List (Fin (n + 1)) := labels.map labelEquiv
  let ys : List ℝ := pieceLengths T
  let sorted : List ℝ := ys.mergeSort (· ≥ ·)
  have hsortedPerm : sorted.Perm ys := by
    exact List.mergeSort_perm ys (· ≥ ·)
  obtain ⟨sortedLabels, hsortedLabelsLen, hsortedLabelsTotal⟩ :=
    permute_labels_preserves_totals hsortedPerm.symm labelsN (by
      simp only [labelsN, List.length_map, ys]
      exact hlabelsLen)
  have hsorted : sorted.Pairwise (· ≥ ·) := by
    have hs := List.pairwise_mergeSort
      (l := ys) (le := fun a b : ℝ => decide (a ≥ b))
      (by
        intro a b c hab hbc
        simp only [decide_eq_true_eq] at hab hbc ⊢
        exact le_trans hbc hab)
      (by
        intro a b
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact le_total b a)
    simpa only [sorted, decide_eq_true_eq] using hs
  have hsortedNonneg : ∀ x ∈ sorted, 0 ≤ x := by
    intro x hx
    have hxy : x ∈ ys := hsortedPerm.mem_iff.mp hx
    exact le_of_lt (pieceLengths_pos T hTint x (by
      simpa only [ys] using hxy))
  have hTcard : T.card ≤ 2 * n := by
    calc
      T.card = (A ∪ B).card := rfl
      _ ≤ A.card + B.card := Finset.card_union_le A B
      _ ≤ n + n := Nat.add_le_add hAcard.le hB.2
      _ = 2 * n := by omega
  have hsortedCard : sorted.length ≤ 2 * (n + 1) - 1 := by
    have hylen : ys.length = T.card + 1 := by
      exact pieceLengths_length T
    have hslen : sorted.length = ys.length := hsortedPerm.length_eq
    omega
  have hsortedSumOne : sorted.sum = 1 := by
    calc
      sorted.sum = ys.sum := hsortedPerm.sum_eq
      _ = 1 := pieceLengths_sum_all T
  have hsortedSum :
      sorted.sum = binaryDelta n * ((2 : ℝ) ^ (n + 1) - 1) := by
    rw [hsortedSumOne, binaryDelta_mul_geom]
  have hsortedGroup : ∀ i : Fin (n + 1),
      labelTotal i sorted sortedLabels = binaryDelta n * (2 : ℝ) ^ (i : ℕ) := by
    intro i
    rw [hsortedLabelsTotal i]
    have hmap := labelTotal_map_equiv labelEquiv (labelEquiv.symm i) ys labels
    rw [labelEquiv.apply_symm_apply] at hmap
    rw [hmap]
    rw [hlabelsTotal (labelEquiv.symm i)]
    let j : Fin (binaryGaps n).length := labelEquiv.symm i
    change (binaryGaps n).get j = binaryDelta n * (2 : ℝ) ^ (i : ℕ)
    dsimp only [binaryGaps] at j ⊢
    rw [List.get_ofFn]
    congr 2
  have hAlt : binaryDelta n * (2 : ℝ) ^ n ≤ alternatingShare sorted :=
    alternatingShare_ge_top_binary_gap n sorted sortedLabels (binaryDelta n)
      hsortedLabelsLen hsortedCard hsorted hsortedNonneg hsortedSum
      hsortedGroup (binaryDelta_pos n)
  have hShare : binaryDelta n * (2 : ℝ) ^ n ≤ firstPlayerShare ys := by
    rw [firstPlayerShare_eq_alternatingShare]
    exact hAlt
  simpa [L, ys, T, binaryDelta, div_eq_mul_inv, mul_comm] using hShare

namespace P3Agent

def pairDup (l : List ℝ) : List ℝ :=
  l.flatMap fun x => [x, x]

@[simp] lemma mem_pairDup {x : ℝ} {l : List ℝ} : x ∈ pairDup l ↔ x ∈ l := by
  simp [pairDup]

lemma pairDup_pairwise {l : List ℝ} (hl : l.Pairwise (· ≥ ·)) :
    (pairDup l).Pairwise (· ≥ ·) := by
  induction l with
  | nil => simp [pairDup]
  | cons x l ih =>
      rw [List.pairwise_cons] at hl
      change (x :: x :: pairDup l).Pairwise (· ≥ ·)
      rw [List.pairwise_cons, List.pairwise_cons]
      refine ⟨?_, ?_, ?_⟩
      · intro y hy
        simp only [List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact le_rfl
        · exact hl.1 y (mem_pairDup.mp hy)
      · intro y hy
        exact hl.1 y (mem_pairDup.mp hy)
      · exact ih hl.2

lemma mergeSort_pairDup (l : List ℝ) :
    (pairDup l).mergeSort (· ≥ ·) = pairDup (l.mergeSort (· ≥ ·)) := by
  have hp : List.Perm ((pairDup l).mergeSort (· ≥ ·))
      (pairDup (l.mergeSort (· ≥ ·))) :=
    (List.mergeSort_perm (pairDup l) _).trans
      ((List.mergeSort_perm l _).symm.flatMap fun _ _ => List.Perm.refl _)
  exact hp.eq_of_pairwise'
    (List.pairwise_mergeSort' (· ≥ ·) (pairDup l))
    (pairDup_pairwise (List.pairwise_mergeSort' (· ≥ ·) l))

def selectedSum (n : ℕ) (l : List ℝ) : ℝ :=
  (((l.zipIdx n).filter (fun p => p.2 % 2 = 0)).map (fun p => p.1)).sum

lemma selectedSum_cons (n : ℕ) (x : ℝ) (l : List ℝ) :
    selectedSum n (x :: l) = (if n % 2 = 0 then x else 0) + selectedSum (n + 1) l := by
  by_cases h : n % 2 = 0 <;> simp [selectedSum, h]

lemma selectedSum_pairDup (n : ℕ) (l : List ℝ) :
    selectedSum n (pairDup l) = l.sum := by
  induction l generalizing n with
  | nil => simp [pairDup, selectedSum]
  | cons x l ih =>
      change selectedSum n (x :: x :: pairDup l) = (x :: l).sum
      rw [selectedSum_cons, selectedSum_cons]
      rw [ih]
      by_cases hn : n % 2 = 0
      · have hn1 : (n + 1) % 2 ≠ 0 := by omega
        simp [hn, hn1]
      · have hnval : n % 2 = 1 := by omega
        have hn1 : (n + 1) % 2 = 0 := by omega
        simp [hn, hn1]

lemma firstPlayerShare_pairDup (l : List ℝ) :
    firstPlayerShare (pairDup l) = l.sum := by
  unfold firstPlayerShare
  rw [mergeSort_pairDup]
  change selectedSum 0 (pairDup (l.mergeSort (· ≥ ·))) = l.sum
  rw [selectedSum_pairDup]
  exact (List.mergeSort_perm l _).sum_eq

lemma sum_pairDup (l : List ℝ) : (pairDup l).sum = 2 * l.sum := by
  induction l with
  | nil => simp [pairDup]
  | cons x l ih =>
      change (x :: x :: pairDup l).sum = 2 * (x :: l).sum
      simp only [List.sum_cons, ih]
      ring

lemma mergeSort_eq_of_perm {l₁ l₂ : List ℝ} (h : l₁.Perm l₂) :
    l₁.mergeSort (· ≥ ·) = l₂.mergeSort (· ≥ ·) := by
  have hp : List.Perm (l₁.mergeSort (· ≥ ·)) (l₂.mergeSort (· ≥ ·)) :=
    (List.mergeSort_perm l₁ _).trans (h.trans (List.mergeSort_perm l₂ _).symm)
  exact hp.eq_of_pairwise'
    (List.pairwise_mergeSort' (· ≥ ·) l₁)
    (List.pairwise_mergeSort' (· ≥ ·) l₂)

lemma firstPlayerShare_eq_of_perm {l₁ l₂ : List ℝ} (h : l₁.Perm l₂) :
    firstPlayerShare l₁ = firstPlayerShare l₂ := by
  unfold firstPlayerShare
  rw [mergeSort_eq_of_perm h]

lemma firstPlayerShare_of_perm_pairDup {L l : List ℝ} (h : L.Perm (pairDup l)) :
    firstPlayerShare L = l.sum := by
  rw [firstPlayerShare_eq_of_perm h, firstPlayerShare_pairDup]

lemma firstPlayerShare_half_total_of_perm_pairDup {L l : List ℝ}
    (h : L.Perm (pairDup l)) : firstPlayerShare L = L.sum / 2 := by
  rw [firstPlayerShare_of_perm_pairDup h, h.sum_eq, sum_pairDup]
  ring

lemma firstPlayerShare_half_of_perm_pairDup {L l : List ℝ}
    (h : L.Perm (pairDup l)) (hsum : L.sum = 1) : firstPlayerShare L = 1 / 2 := by
  rw [firstPlayerShare_half_total_of_perm_pairDup h, hsum]

def signedAlt : List ℝ → ℝ
  | [] => 0
  | a :: t => a - signedAlt t

lemma twice_alternatingShare_signedAlt (l : List ℝ) :
    2 * alternatingShare l = l.sum + signedAlt l := by
  induction l using List.twoStepInduction with
  | nil => simp [alternatingShare, signedAlt]
  | singleton a =>
      simp [alternatingShare, signedAlt]
      ring
  | cons_cons a b t ih =>
      simp only [alternatingShare, signedAlt, List.sum_cons]
      linarith

lemma signedAlt_bounds {l : List ℝ} (hsort : l.Pairwise (· ≥ ·))
    (hnonneg : ∀ x ∈ l, 0 ≤ x) :
    0 ≤ signedAlt l ∧ ∀ a t, l = a :: t → signedAlt l ≤ a := by
  induction l with
  | nil =>
      simp [signedAlt]
  | cons a t ih =>
      have htSort : t.Pairwise (· ≥ ·) := (List.pairwise_cons.mp hsort).2
      have htNonneg : ∀ x ∈ t, 0 ≤ x := by
        intro x hx
        exact hnonneg x (by simp [hx])
      obtain ⟨ht0, htHead⟩ := ih htSort htNonneg
      constructor
      · cases t with
        | nil => simp [signedAlt, hnonneg a (by simp)]
        | cons b t =>
            have hDb : signedAlt (b :: t) ≤ b := htHead b t rfl
            have hab : b ≤ a := (List.pairwise_cons.mp hsort).1 b (by simp)
            change 0 ≤ a - signedAlt (b :: t)
            linarith
      · intro b u heq
        simp only [List.cons.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        change a - signedAlt t ≤ a
        linarith

lemma abs_signedAlt_orderedInsert_sub_le (a : ℝ) (ha : 0 ≤ a) {l : List ℝ}
    (hsort : l.Pairwise (· ≥ ·)) (hnonneg : ∀ x ∈ l, 0 ≤ x) :
    |signedAlt (l.orderedInsert (· ≥ ·) a) - signedAlt l| ≤ a := by
  induction l with
  | nil =>
      simp [signedAlt, abs_of_nonneg ha]
  | cons b t ih =>
      have htSort : t.Pairwise (· ≥ ·) := (List.pairwise_cons.mp hsort).2
      have htNonneg : ∀ x ∈ t, 0 ≤ x := by
        intro x hx
        exact hnonneg x (by simp [hx])
      by_cases hab : a ≥ b
      · rw [List.orderedInsert_cons_of_le (r := (· ≥ ·)) t hab]
        change |(a - signedAlt (b :: t)) - signedAlt (b :: t)| ≤ a
        obtain ⟨hD0, hDhead⟩ := signedAlt_bounds hsort hnonneg
        have hDb : signedAlt (b :: t) ≤ b := hDhead b t rfl
        rw [abs_le]
        constructor <;> linarith
      · rw [List.orderedInsert_of_not_le (r := (· ≥ ·)) t hab]
        change |(b - signedAlt (t.orderedInsert (· ≥ ·) a)) -
          (b - signedAlt t)| ≤ a
        rw [show (b - signedAlt (t.orderedInsert (· ≥ ·) a)) -
          (b - signedAlt t) =
            -(signedAlt (t.orderedInsert (· ≥ ·) a) - signedAlt t) by ring,
          abs_neg]
        exact ih htSort htNonneg

lemma mergeSort_cons_eq_orderedInsert (a : ℝ) (l : List ℝ) :
    (a :: l).mergeSort (· ≥ ·) =
      (l.mergeSort (· ≥ ·)).orderedInsert (· ≥ ·) a := by
  rw [List.mergeSort_eq_insertionSort (r := (· ≥ ·)),
    List.insertionSort_cons,
    List.mergeSort_eq_insertionSort (r := (· ≥ ·))]

lemma firstPlayerShare_cons_le (a : ℝ) (l : List ℝ) (ha : 0 ≤ a)
    (hnonneg : ∀ x ∈ l, 0 ≤ x) :
    firstPlayerShare (a :: l) ≤ firstPlayerShare l + a := by
  let s := l.mergeSort (· ≥ ·)
  have hsperm : s.Perm l := List.mergeSort_perm l (· ≥ ·)
  have hsort : s.Pairwise (· ≥ ·) := List.pairwise_mergeSort' (· ≥ ·) l
  have hsn : ∀ x ∈ s, 0 ≤ x := by
    intro x hx
    exact hnonneg x (hsperm.mem_iff.mp hx)
  let ins := s.orderedInsert (· ≥ ·) a
  have hDabs : |signedAlt ins - signedAlt s| ≤ a := by
    exact abs_signedAlt_orderedInsert_sub_le a ha hsort hsn
  have hD : signedAlt ins - signedAlt s ≤ a :=
    (le_abs_self _).trans hDabs
  have hsumIns : ins.sum = a + s.sum := by
    have hp := List.perm_orderedInsert (· ≥ ·) a s
    have := hp.sum_eq
    simpa [ins] using this
  have htwIns := twice_alternatingShare_signedAlt ins
  have htwS := twice_alternatingShare_signedAlt s
  rw [firstPlayerShare_eq_alternatingShare,
    firstPlayerShare_eq_alternatingShare, mergeSort_cons_eq_orderedInsert]
  change alternatingShare ins ≤ alternatingShare s + a
  linarith

lemma firstPlayerShare_pairDup_append_le_of_nonneg (q r : List ℝ)
    (hq : ∀ x ∈ q, 0 ≤ x) (hr : ∀ x ∈ r, 0 ≤ x) :
    firstPlayerShare (pairDup q ++ r) ≤ q.sum + r.sum := by
  induction r with
  | nil =>
      simp only [List.append_nil, List.sum_nil, add_zero]
      exact le_of_eq (firstPlayerShare_pairDup q)
  | cons a r ih =>
      have ha : 0 ≤ a := hr a (by simp)
      have hr' : ∀ x ∈ r, 0 ≤ x := by
        intro x hx
        exact hr x (by simp [hx])
      have hbase : ∀ x ∈ pairDup q ++ r, 0 ≤ x := by
        intro x hx
        rw [List.mem_append] at hx
        rcases hx with hx | hx
        · exact hq x (mem_pairDup.mp hx)
        · exact hr' x hx
      calc
        firstPlayerShare (pairDup q ++ a :: r) =
            firstPlayerShare (a :: (pairDup q ++ r)) :=
          firstPlayerShare_eq_of_perm List.perm_middle
        _ ≤ firstPlayerShare (pairDup q ++ r) + a :=
          firstPlayerShare_cons_le a (pairDup q ++ r) ha hbase
        _ ≤ (q.sum + r.sum) + a := by
          simpa [add_comm] using add_le_add_right (ih hr') a
        _ = q.sum + (a :: r).sum := by simp; ring

lemma firstPlayerShare_perm_pairDup_append_le_of_nonneg {L q r : List ℝ}
    (hperm : L.Perm (pairDup q ++ r))
    (hq : ∀ x ∈ q, 0 ≤ x) (hr : ∀ x ∈ r, 0 ≤ x) :
    firstPlayerShare L ≤ q.sum + r.sum := by
  rw [firstPlayerShare_eq_of_perm hperm]
  exact firstPlayerShare_pairDup_append_le_of_nonneg q r hq hr

end P3Agent

namespace LiuBangXiangYuUpperScratch

abbrev doubleList := P3Agent.pairDup

@[simp] lemma doubleList_sum (q : List ℝ) :
    (doubleList q).sum = 2 * q.sum := P3Agent.sum_pairDup q

lemma doubleList_eq_flatMap (q : List ℝ) :
    doubleList q = q.flatMap (fun x => [x, x]) := rfl

section CloseSubsetSums

noncomputable def unitBin (D : ℕ) (hD : 0 < D) (x : ℝ) : Fin D :=
  ⟨min ⌊(D : ℝ) * x⌋₊ (D - 1), by omega⟩

lemma unitBin_bounds (D : ℕ) (hD : 0 < D) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ((unitBin D hD x : ℕ) : ℝ) ≤ (D : ℝ) * x ∧
      (D : ℝ) * x ≤ ((unitBin D hD x : ℕ) : ℝ) + 1 := by
  let k : ℕ := ⌊(D : ℝ) * x⌋₊
  have hDx : 0 ≤ (D : ℝ) * x := mul_nonneg (Nat.cast_nonneg D) hx.1
  have hklo : (k : ℝ) ≤ (D : ℝ) * x := Nat.floor_le hDx
  have hkhi : (D : ℝ) * x < (k : ℝ) + 1 := by
    simpa [k] using (Nat.lt_succ_floor ((D : ℝ) * x))
  change ((min k (D - 1) : ℕ) : ℝ) ≤ (D : ℝ) * x ∧
    (D : ℝ) * x ≤ ((min k (D - 1) : ℕ) : ℝ) + 1
  constructor
  · exact (Nat.cast_le.mpr (min_le_left k (D - 1))).trans hklo
  · by_cases hk : k ≤ D - 1
    · rw [min_eq_left hk]
      exact hkhi.le
    · have hmin : min k (D - 1) = D - 1 := min_eq_right (le_of_not_ge hk)
      rw [hmin]
      have hcastD : ((D - 1 : ℕ) : ℝ) + 1 = D := by
        rw [Nat.cast_sub (by omega : 1 ≤ D)]
        norm_num
      rw [hcastD]
      simpa using mul_le_mul_of_nonneg_left hx.2 (Nat.cast_nonneg D)

lemma abs_sub_le_inv_of_unitBin_eq (D : ℕ) (hD : 0 < D)
    {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hbin : unitBin D hD x = unitBin D hD y) :
    |x - y| ≤ 1 / D := by
  have hxB := unitBin_bounds D hD x hx
  have hyB := unitBin_bounds D hD y hy
  have hval : (unitBin D hD x : ℕ) = (unitBin D hD y : ℕ) :=
    congrArg Fin.val hbin
  rw [hval] at hxB
  have hDreal : (0 : ℝ) < D := Nat.cast_pos.mpr hD
  rw [abs_le]
  constructor
  · have hyx : y - x ≤ 1 / (D : ℝ) := by
      apply (le_div_iff₀ hDreal).2
      nlinarith
    linarith
  · apply (le_div_iff₀ hDreal).2
    nlinarith

lemma finset_sum_mem_Icc_of_nonneg {m : ℕ} (w : Fin m → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (s : Finset (Fin m)) :
    ∑ i ∈ s, w i ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.sum_nonneg fun i _ => hw i
  · calc
      ∑ i ∈ s, w i ≤ ∑ i, w i :=
        Finset.sum_le_univ_sum_of_nonneg hw
      _ = 1 := hsum

/-- Among the `2^m` subset sums of `m` nonnegative weights totaling one,
two distinct subset sums are within `1 / (2^m - 1)`. -/
lemma exists_close_subset_sums {m : ℕ} (hm : 0 < m) (w : Fin m → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    ∃ s t : Finset (Fin m), s ≠ t ∧
      |∑ i ∈ s, w i - ∑ i ∈ t, w i| ≤ 1 / ((2 ^ m - 1 : ℕ) : ℝ) := by
  let D : ℕ := 2 ^ m - 1
  have hpow : 1 < 2 ^ m := by
    exact one_lt_pow₀ (by decide : 1 < (2 : ℕ)) hm.ne'
  have hD : 0 < D := by omega
  let f : Finset (Fin m) → Fin D := fun s =>
    unitBin D hD (∑ i ∈ s, w i)
  have hcardDom : Fintype.card (Finset (Fin m)) = 2 ^ m := by simp
  have hcardCod : Fintype.card (Fin D) = D := Fintype.card_fin D
  have hlt : Fintype.card (Fin D) < Fintype.card (Finset (Fin m)) := by
    rw [hcardDom, hcardCod]
    dsimp [D]
    omega
  rcases Fintype.exists_ne_map_eq_of_card_lt f hlt with ⟨s, t, hst, hft⟩
  refine ⟨s, t, hst, ?_⟩
  simpa [D] using abs_sub_le_inv_of_unitBin_eq D hD
    (finset_sum_mem_Icc_of_nonneg w hw hsum s)
    (finset_sum_mem_Icc_of_nonneg w hw hsum t) hft

end CloseSubsetSums

section CancelSubsetSums

lemma sum_sub_sum_eq_sdiff_sub_sdiff {m : ℕ} (w : Fin m → ℝ)
    (s t : Finset (Fin m)) :
    (∑ i ∈ s, w i) - ∑ i ∈ t, w i =
      (∑ i ∈ s \ t, w i) - ∑ i ∈ t \ s, w i := by
  have hs : (∑ i ∈ s, w i) =
      (∑ i ∈ s \ t, w i) + ∑ i ∈ s ∩ t, w i := by
    calc
      ∑ i ∈ s, w i = ∑ i ∈ (s \ t) ∪ (s ∩ t), w i := by
        rw [Finset.sdiff_union_inter]
      _ = (∑ i ∈ s \ t, w i) + ∑ i ∈ s ∩ t, w i :=
        Finset.sum_union (Finset.disjoint_left.mpr (by
          intro a ha hb
          exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_inter.mp hb).2))
  have ht : (∑ i ∈ t, w i) =
      (∑ i ∈ t \ s, w i) + ∑ i ∈ s ∩ t, w i := by
    calc
      ∑ i ∈ t, w i = (∑ i ∈ t \ s, w i) + ∑ i ∈ t ∩ s, w i := by
        calc
          ∑ i ∈ t, w i = ∑ i ∈ (t \ s) ∪ (t ∩ s), w i := by
            rw [Finset.sdiff_union_inter]
          _ = (∑ i ∈ t \ s, w i) + ∑ i ∈ t ∩ s, w i :=
            Finset.sum_union (Finset.disjoint_left.mpr (by
              intro a ha hb
              exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_inter.mp hb).2))
      _ = (∑ i ∈ t \ s, w i) + ∑ i ∈ s ∩ t, w i := by
        rw [Finset.inter_comm]
  rw [hs, ht]
  ring

lemma sdiff_nonempty_or_sdiff_nonempty_of_ne {m : ℕ}
    {s t : Finset (Fin m)} (hst : s ≠ t) :
    (s \ t).Nonempty ∨ (t \ s).Nonempty := by
  by_contra h
  push Not at h
  have hp : s \ t = ∅ := h.1
  have hq : t \ s = ∅ := h.2
  apply hst
  exact Finset.Subset.antisymm
    (Finset.sdiff_eq_empty_iff_subset.mp hp)
    (Finset.sdiff_eq_empty_iff_subset.mp hq)

/-- Canceling the common part of close subset sums gives disjoint nontrivial
collections, oriented so the first has the larger sum. -/
lemma exists_disjoint_close_subset_sums {m : ℕ} (hm : 0 < m)
    (w : Fin m → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    ∃ p q : Finset (Fin m), Disjoint p q ∧
      (p.Nonempty ∨ q.Nonempty) ∧
      (∑ i ∈ q, w i) ≤ ∑ i ∈ p, w i ∧
      (∑ i ∈ p, w i) - ∑ i ∈ q, w i ≤
        1 / ((2 ^ m - 1 : ℕ) : ℝ) := by
  rcases exists_close_subset_sums hm w hw hsum with ⟨s, t, hst, hclose⟩
  let p₀ := s \ t
  let q₀ := t \ s
  have hne : p₀.Nonempty ∨ q₀.Nonempty :=
    sdiff_nonempty_or_sdiff_nonempty_of_ne hst
  have hd : Disjoint p₀ q₀ := by
    simp only [Finset.disjoint_left, p₀, q₀, Finset.mem_sdiff]
    aesop
  have hdiff : (∑ i ∈ s, w i) - ∑ i ∈ t, w i =
      (∑ i ∈ p₀, w i) - ∑ i ∈ q₀, w i := by
    simpa [p₀, q₀] using sum_sub_sum_eq_sdiff_sub_sdiff w s t
  rw [hdiff] at hclose
  by_cases horient : (∑ i ∈ q₀, w i) ≤ ∑ i ∈ p₀, w i
  · refine ⟨p₀, q₀, hd, hne, horient, ?_⟩
    exact (le_abs_self _).trans hclose
  · refine ⟨q₀, p₀, hd.symm, hne.symm, le_of_not_ge horient, ?_⟩
    simpa [sub_eq_add_neg, add_comm] using (neg_le_abs
      ((∑ i ∈ p₀, w i) - ∑ i ∈ q₀, w i)).trans hclose

end CancelSubsetSums

section CommonRefinement

/-- `ys` refines `xs` when each entry of `xs` is replaced, in order, by a
nonempty block of entries having the same sum. -/
abbrev Refines := P3Realization.Refines
abbrev Refines.nil : Refines [] [] := P3Realization.Refines.nil
abbrev Refines.cons {x : ℝ} {xs ys : List ℝ} (u : List ℝ) (hu : u ≠ [])
    (hsum : u.sum = x) (hrest : Refines xs ys) : Refines (x :: xs) (u ++ ys) :=
  P3Realization.Refines.cons u hu hsum hrest

lemma Refines.refl (xs : List ℝ) : Refines xs xs := by
  induction xs with
  | nil => exact Refines.nil
  | cons x xs ih =>
      simpa using Refines.cons [x] (by simp) (by simp) ih

lemma Refines.cons_single {xs ys : List ℝ} (x : ℝ) (h : Refines xs ys) :
    Refines (x :: xs) (x :: ys) := by
  simpa using Refines.cons [x] (by simp) (by simp) h

/-- Add a new fine piece to the first coarse block, increasing that coarse
entry by the same amount. -/
lemma Refines.prepend_to_first {x : ℝ} {xs ys : List ℝ}
    (a : ℝ) (h : Refines (x :: xs) ys) :
    Refines ((a + x) :: xs) (a :: ys) := by
  cases h with
  | cons u hu hsum hrest =>
      exact Refines.cons (a :: u) (by simp) (by simp [hsum]) hrest

/-- Overlay two positive partitions, with the second no longer than the first.
The matched pieces `q` occur once on each side; `r` is precisely the unmatched
positive remainder on the longer side.  The sharp length estimate is the
usual `p+q-1` common-refinement cut count. -/
lemma exists_common_refinement (xs ys : List ℝ) (hxs : xs ≠ [])
    (hxpos : ∀ x ∈ xs, 0 < x) (hypos : ∀ y ∈ ys, 0 < y)
    (hsumle : ys.sum ≤ xs.sum) :
    ∃ q r : List ℝ,
      Refines xs (q ++ r) ∧ Refines ys q ∧
      (∀ z ∈ q, 0 < z) ∧ (∀ z ∈ r, 0 < z) ∧
      2 * q.length + r.length ≤ 2 * (xs.length + ys.length) - 1 ∧
      r.sum = xs.sum - ys.sum := by
  generalize hN : xs.length + ys.length = N
  induction N using Nat.strong_induction_on generalizing xs ys with
  | h N ih =>
      cases xs with
      | nil => exact (hxs rfl).elim
      | cons x xt =>
          cases ys with
          | nil =>
              refine ⟨[], x :: xt, ?_, Refines.nil, ?_, ?_, ?_, ?_⟩
              · simpa using Refines.refl (x :: xt)
              · simp
              · exact hxpos
              · simp only [List.length_nil, List.length_cons, add_zero] at hN ⊢
                omega
              · simp
          | cons y yt =>
              simp only [List.length_cons] at hN
              have hx : 0 < x := hxpos x (by simp)
              have hy : 0 < y := hypos y (by simp)
              have hxtpos : ∀ z ∈ xt, 0 < z := by
                intro z hz
                exact hxpos z (by simp [hz])
              have hytpos : ∀ z ∈ yt, 0 < z := by
                intro z hz
                exact hypos z (by simp [hz])
              rcases lt_trichotomy x y with hxy | hxy | hxy
              · -- The first left piece is exhausted; split the first right piece.
                have hdiff : 0 < y - x := sub_pos.mpr hxy
                have hnewle : ((y - x) :: yt).sum ≤ xt.sum := by
                  simp only [List.sum_cons] at hsumle ⊢
                  linarith
                have hxtne : xt ≠ [] := by
                  intro he
                  subst xt
                  simp only [List.sum_cons, List.sum_nil] at hnewle
                  have htailnonneg : 0 ≤ yt.sum := List.sum_nonneg fun z hz =>
                    (hytpos z hz).le
                  linarith
                have hmeasure : xt.length + ((y - x) :: yt).length < N := by
                  simp only [List.length_cons] at hN ⊢
                  omega
                rcases ih _ hmeasure xt ((y - x) :: yt) hxtne hxtpos
                    (by
                      intro z hz
                      simp only [List.mem_cons] at hz
                      rcases hz with rfl | hz
                      · exact hdiff
                      · exact hytpos z hz)
                    hnewle rfl with ⟨q, r, hPx, hQy, hqpos, hrpos, hlen, hrsum⟩
                refine ⟨x :: q, r, ?_, ?_, ?_, hrpos, ?_, ?_⟩
                · simpa [List.cons_append] using Refines.cons_single x hPx
                · have hadd := Refines.prepend_to_first x hQy
                  simpa [sub_eq_add_neg, add_assoc, sub_add_cancel] using hadd
                · intro z hz
                  simp only [List.mem_cons] at hz
                  exact hz.elim (fun h => h ▸ hx) (hqpos z)
                · simp only [List.length_cons] at hlen ⊢
                  omega
                · simp only [List.sum_cons] at hrsum ⊢
                  linarith
              · -- Equal heads are already one matched pair.
                subst y
                have htaille : yt.sum ≤ xt.sum := by
                  simp only [List.sum_cons] at hsumle
                  linarith
                by_cases hxt : xt = []
                · subst xt
                  have hyt : yt = [] := by
                    by_contra hne
                    have hp := P3Realization.sum_pos_of_pos_of_ne_nil yt hne hytpos
                    simp only [List.sum_nil] at htaille
                    linarith
                  subst yt
                  refine ⟨[x], [], ?_, ?_, ?_, ?_, ?_, ?_⟩
                  · simpa using Refines.cons_single x Refines.nil
                  · exact Refines.cons_single x Refines.nil
                  · simpa using hx
                  · simp
                  · simp only [List.length_cons, List.length_nil, add_zero] at hN ⊢
                    omega
                  · simp
                · have hmeasure : xt.length + yt.length < N := by
                    omega
                  rcases ih _ hmeasure xt yt hxt hxtpos hytpos htaille rfl with
                    ⟨q, r, hPx, hQy, hqpos, hrpos, hlen, hrsum⟩
                  refine ⟨x :: q, r, ?_, ?_, ?_, hrpos, ?_, ?_⟩
                  · simpa [List.cons_append] using Refines.cons_single x hPx
                  · exact Refines.cons_single x hQy
                  · intro z hz
                    simp only [List.mem_cons] at hz
                    exact hz.elim (fun h => h ▸ hx) (hqpos z)
                  · simp only [List.length_cons] at hlen ⊢
                    omega
                  · simp only [List.sum_cons] at hrsum ⊢
                    linarith
              · -- The first right piece is exhausted; split the first left piece.
                have hdiff : 0 < x - y := sub_pos.mpr hxy
                have hnewle : yt.sum ≤ ((x - y) :: xt).sum := by
                  simp only [List.sum_cons] at hsumle ⊢
                  linarith
                have hmeasure : ((x - y) :: xt).length + yt.length < N := by
                  simp only [List.length_cons] at hN ⊢
                  omega
                rcases ih _ hmeasure ((x - y) :: xt) yt (by simp) (by
                    intro z hz
                    simp only [List.mem_cons] at hz
                    rcases hz with rfl | hz
                    · exact hdiff
                    · exact hxtpos z hz)
                    hytpos hnewle rfl with
                  ⟨q, r, hPx, hQy, hqpos, hrpos, hlen, hrsum⟩
                refine ⟨y :: q, r, ?_, ?_, ?_, hrpos, ?_, ?_⟩
                · have hadd := Refines.prepend_to_first y hPx
                  simpa [sub_eq_add_neg, add_assoc, sub_add_cancel] using hadd
                · exact Refines.cons_single y hQy
                · intro z hz
                  simp only [List.mem_cons] at hz
                  exact hz.elim (fun h => h ▸ hy) (hqpos z)
                · simp only [List.length_cons] at hlen ⊢
                  omega
                · simp only [List.sum_cons] at hrsum ⊢
                  linarith

end CommonRefinement

section AssembleRefinements

variable {α : Type*} [DecidableEq α]

def selectWeights (is : List α) (p : Finset α) (w : α → ℝ) : List ℝ :=
  (is.filter fun i => i ∈ p).map w

def remainingWeights (is : List α) (p q : Finset α) (w : α → ℝ) : List ℝ :=
  (is.filter fun i => i ∉ p ∧ i ∉ q).map w

noncomputable def bisectPieces (l : List ℝ) : List ℝ :=
  l.flatMap fun x => [x / 2, x / 2]

lemma bisectPieces_eq_doubleList_map (l : List ℝ) :
    bisectPieces l = doubleList (l.map (· / 2)) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      change [x / 2, x / 2] ++ bisectPieces xs =
        (x / 2) :: (x / 2) :: doubleList (xs.map (· / 2))
      simp [ih]

/-- Interleave refinements of two disjoint selected sublists and bisections of
all remaining entries back into the original physical order. -/
lemma assemble_refinements (is : List α) (w : α → ℝ)
    (p q : Finset α) (hd : Disjoint p q)
    (fp fq : List ℝ)
    (hp : Refines (selectWeights is p w) fp)
    (hq : Refines (selectWeights is q w) fq)
    (hwpos : ∀ i ∈ is, 0 < w i)
    (hfppos : ∀ z ∈ fp, 0 < z) (hfqpos : ∀ z ∈ fq, 0 < z) :
    ∃ l : List ℝ,
      Refines (is.map w) l ∧
      l.Perm (fp ++ fq ++ bisectPieces (remainingWeights is p q w)) ∧
      ∀ z ∈ l, 0 < z := by
  induction is generalizing fp fq with
  | nil =>
      simp only [selectWeights, List.filter_nil, List.map_nil] at hp hq
      cases hp
      cases hq
      refine ⟨[], Refines.nil, ?_, ?_⟩ <;>
        simp [remainingWeights, bisectPieces]
  | cons i is ih =>
      have hiw : 0 < w i := hwpos i (by simp)
      have htailpos : ∀ j ∈ is, 0 < w j := by
        intro j hj
        exact hwpos j (by simp [hj])
      by_cases hip : i ∈ p
      · have hiq : i ∉ q := by
          intro hiq
          exact Finset.disjoint_left.mp hd hip hiq
        simp [selectWeights, hip] at hp
        simp [selectWeights, hiq] at hq
        cases hp with
        | @cons x' xs' fpTail u hu husum hpTail =>
            have hupos : ∀ z ∈ u, 0 < z := by
              intro z hz
              exact hfppos z (by simp [hz])
            have hpTailpos : ∀ z ∈ fpTail, 0 < z := by
              intro z hz
              exact hfppos z (by simp [hz])
            rcases ih fpTail fq hpTail hq htailpos hpTailpos hfqpos with
              ⟨l, href, hperm, hlpos⟩
            refine ⟨u ++ l, ?_, ?_, ?_⟩
            · simpa using Refines.cons u hu husum href
            · have happ := hperm.append_left u
              simpa [remainingWeights, hip, hiq, List.append_assoc] using happ
            · intro z hz
              rw [List.mem_append] at hz
              exact hz.elim (hupos z) (hlpos z)
      · by_cases hiq : i ∈ q
        · simp [selectWeights, hip] at hp
          simp [selectWeights, hiq] at hq
          cases hq with
          | @cons x' xs' fqTail u hu husum hqTail =>
              have hupos : ∀ z ∈ u, 0 < z := by
                intro z hz
                exact hfqpos z (by simp [hz])
              have hqTailpos : ∀ z ∈ fqTail, 0 < z := by
                intro z hz
                exact hfqpos z (by simp [hz])
              rcases ih fp fqTail hp hqTail htailpos hfppos hqTailpos with
                ⟨l, href, hperm, hlpos⟩
              refine ⟨u ++ l, ?_, ?_, ?_⟩
              · simpa using Refines.cons u hu husum href
              · have hstart : (u ++ l).Perm
                    (u ++ (fp ++ fqTail ++ bisectPieces
                      (remainingWeights is p q w))) := hperm.append_left u
                have hswap : (u ++ fp).Perm (fp ++ u) := List.perm_append_comm
                have hgroup := hswap.append_right
                  (fqTail ++ bisectPieces (remainingWeights is p q w))
                exact hstart.trans (by
                  simpa [remainingWeights, hip, hiq, List.append_assoc] using hgroup)
              · intro z hz
                rw [List.mem_append] at hz
                exact hz.elim (hupos z) (hlpos z)
        · simp [selectWeights, hip] at hp
          simp [selectWeights, hiq] at hq
          rcases ih fp fq hp hq htailpos hfppos hfqpos with
            ⟨l, href, hperm, hlpos⟩
          let u : List ℝ := [w i / 2, w i / 2]
          have hupos : ∀ z ∈ u, 0 < z := by
            intro z hz
            have hz' : z = w i / 2 := by simpa [u] using hz
            subst z
            linarith
          refine ⟨u ++ l, ?_, ?_, ?_⟩
          · exact Refines.cons u (by simp [u]) (by simp [u]) href
          · have hstart : (u ++ l).Perm
                (u ++ (fp ++ fq ++ bisectPieces
                  (remainingWeights is p q w))) := hperm.append_left u
            have hswap : (u ++ (fp ++ fq)).Perm ((fp ++ fq) ++ u) :=
              List.perm_append_comm
            have hgroup := hswap.append_right
              (bisectPieces (remainingWeights is p q w))
            exact hstart.trans (by
              simpa [remainingWeights, hip, hiq, bisectPieces, u,
                List.append_assoc] using hgroup)
          · intro z hz
            rw [List.mem_append] at hz
            exact hz.elim (hupos z) (hlpos z)

end AssembleRefinements

section IndexedWeights

lemma sum_map_eq_sum_toFinset {α : Type*} [DecidableEq α]
    (l : List α) (w : α → ℝ) (hl : l.Nodup) :
    (l.map w).sum = ∑ i ∈ l.toFinset, w i := by
  induction l with
  | nil => simp
  | cons i is ih =>
      rw [List.nodup_cons] at hl
      simp [hl.1, ih hl.2]

lemma filter_finRange_toFinset {m : ℕ} (p : Finset (Fin m)) :
    ((List.finRange m).filter fun i => i ∈ p).toFinset = p := by
  ext i
  simp

lemma selectWeights_finRange_sum' {m : ℕ} (w : Fin m → ℝ)
    (p : Finset (Fin m)) :
    (selectWeights (List.finRange m) p w).sum = ∑ i ∈ p, w i := by
  rw [selectWeights, sum_map_eq_sum_toFinset]
  · rw [filter_finRange_toFinset]
  · exact (List.nodup_finRange m).filter _

lemma selectWeights_finRange_length {m : ℕ} (w : Fin m → ℝ)
    (p : Finset (Fin m)) :
    (selectWeights (List.finRange m) p w).length = p.card := by
  rw [selectWeights, List.length_map]
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange m).filter _)]
  rw [filter_finRange_toFinset]

lemma selectWeights_finRange_pos {m : ℕ} (w : Fin m → ℝ)
    (hw : ∀ i, 0 < w i) (p : Finset (Fin m)) :
    ∀ z ∈ selectWeights (List.finRange m) p w, 0 < z := by
  intro z hz
  simp only [selectWeights, List.mem_map] at hz
  rcases hz with ⟨i, hi, rfl⟩
  exact hw i

lemma remainingWeights_finRange_length {m : ℕ} (w : Fin m → ℝ)
    (p q : Finset (Fin m)) (hd : Disjoint p q) :
    (remainingWeights (List.finRange m) p q w).length =
      m - (p.card + q.card) := by
  rw [remainingWeights, List.length_map]
  have hnodup := (List.nodup_finRange m).filter
    (fun i => i ∉ p ∧ i ∉ q)
  rw [← List.toFinset_card_of_nodup hnodup]
  have hset : ((List.finRange m).filter fun i => i ∉ p ∧ i ∉ q).toFinset =
      Finset.univ \ (p ∪ q) := by
    ext i
    simp
  rw [hset, Finset.card_sdiff]
  simp only [Finset.inter_univ, Finset.card_univ, Fintype.card_fin,
    Finset.card_union_of_disjoint hd]

lemma remainingWeights_finRange_pos {m : ℕ} (w : Fin m → ℝ)
    (hw : ∀ i, 0 < w i) (p q : Finset (Fin m)) :
    ∀ z ∈ remainingWeights (List.finRange m) p q w, 0 < z := by
  intro z hz
  simp only [remainingWeights, List.mem_map] at hz
  rcases hz with ⟨i, hi, rfl⟩
  exact hw i

lemma doubleList_append (a b : List ℝ) :
    doubleList (a ++ b) = doubleList a ++ doubleList b := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [doubleList, P3Agent.pairDup]

lemma doubleList_length (a : List ℝ) :
    (doubleList a).length = 2 * a.length := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [doubleList, P3Agent.pairDup]; omega

lemma append_self_perm_doubleList (q : List ℝ) :
    (q ++ q).Perm (doubleList q) := by
  rw [doubleList_eq_flatMap]
  simpa using List.flatMap_append_perm q (fun x : ℝ => [x]) (fun x : ℝ => [x])

lemma paired_assembly_perm (q r h : List ℝ) :
    ((q ++ r) ++ q ++ doubleList h).Perm
      (doubleList (q ++ h) ++ r) := by
  have hcomm : (r ++ (q ++ doubleList h)).Perm
      ((q ++ doubleList h) ++ r) := List.perm_append_comm
  have hmove : (q ++ (r ++ (q ++ doubleList h))).Perm
      (q ++ ((q ++ doubleList h) ++ r)) := hcomm.append_left q
  have hdup := (append_self_perm_doubleList q).append_right (doubleList h ++ r)
  have hmove' : ((q ++ r) ++ q ++ doubleList h).Perm
      ((q ++ q) ++ doubleList h ++ r) := by
    simpa [List.append_assoc] using hmove
  have hdup' : ((q ++ q) ++ doubleList h ++ r).Perm
      (doubleList (q ++ h) ++ r) := by
    simpa [doubleList_append, List.append_assoc] using hdup
  exact hmove'.trans hdup'

end IndexedWeights

section FullCardinalityStrategy

/-- Pure list form of the hard (`A.card = n`) construction.  It returns a
positive refinement with at most twice as many pieces minus one, whose
multiset is paired except for residual pieces of total at most the exact
binary-pigeonhole error. -/
lemma exists_paired_refinement (g : List ℝ) (hne : g ≠ [])
    (hpos : ∀ x ∈ g, 0 < x) (hsum : g.sum = 1) :
    ∃ l paired residual : List ℝ,
      Refines g l ∧ l.Perm (doubleList paired ++ residual) ∧
      (∀ z ∈ l, 0 < z) ∧ (∀ z ∈ paired, 0 < z) ∧
      (∀ z ∈ residual, 0 < z) ∧
      l.length ≤ 2 * g.length - 1 ∧
      residual.sum ≤ 1 / ((2 ^ g.length - 1 : ℕ) : ℝ) := by
  let m := g.length
  let w : Fin m → ℝ := g.get
  let is : List (Fin m) := List.finRange m
  have hm : 0 < m := by
    apply Nat.pos_of_ne_zero
    intro hm0
    apply hne
    exact List.eq_nil_of_length_eq_zero hm0
  have hw : ∀ i, 0 < w i := by
    intro i
    exact hpos (g.get i) (List.get_mem g i)
  have hsumw : ∑ i, w i = 1 := by
    rw [← List.sum_ofFn, List.ofFn_get, hsum]
  rcases exists_disjoint_close_subset_sums hm w (fun i => (hw i).le) hsumw with
    ⟨p, q, hd, hpqne, horient, hclose⟩
  let xp := selectWeights is p w
  let yq := selectWeights is q w
  let rem := remainingWeights is p q w
  have hxpsum : xp.sum = ∑ i ∈ p, w i := by
    simpa [xp, is] using selectWeights_finRange_sum' w p
  have hyqsum : yq.sum = ∑ i ∈ q, w i := by
    simpa [yq, is] using selectWeights_finRange_sum' w q
  have hxppos : ∀ z ∈ xp, 0 < z := by
    simpa [xp, is] using selectWeights_finRange_pos w hw p
  have hyqpos : ∀ z ∈ yq, 0 < z := by
    simpa [yq, is] using selectWeights_finRange_pos w hw q
  have hpne : p.Nonempty := by
    by_cases hp : p.Nonempty
    · exact hp
    · exfalso
      have hq : q.Nonempty := hpqne.resolve_left hp
      have hqcard : 0 < q.card := Finset.card_pos.mpr hq
      have hyqlen : yq.length = q.card := by
        simpa [yq, is] using selectWeights_finRange_length w q
      have hyqne : yq ≠ [] := by
        intro he
        have := congrArg List.length he
        simp only [List.length_nil, hyqlen] at this
        omega
      have hyqsumpos := P3Realization.sum_pos_of_pos_of_ne_nil yq hyqne hyqpos
      have hpempty : p = ∅ := Finset.not_nonempty_iff_eq_empty.mp hp
      have hxpempty : xp = [] := by
        apply List.eq_nil_of_length_eq_zero
        rw [show xp.length = p.card by
          simpa [xp, is] using selectWeights_finRange_length w p, hpempty]
        simp
      have hlistorient : yq.sum ≤ xp.sum := by
        rw [hxpsum, hyqsum]
        exact horient
      rw [hxpempty] at hlistorient
      simp only [List.sum_nil] at hlistorient
      linarith
  have hxpne : xp ≠ [] := by
    intro he
    have hplen : xp.length = p.card := by
      simpa [xp, is] using selectWeights_finRange_length w p
    have := congrArg List.length he
    simp only [List.length_nil, hplen] at this
    exact (Finset.card_pos.mpr hpne).ne' this
  have hlistorient : yq.sum ≤ xp.sum := by
    rw [hxpsum, hyqsum]
    exact horient
  rcases exists_common_refinement xp yq hxpne hxppos hyqpos hlistorient with
    ⟨matched, residual, hxpRef, hyqRef, hmatchedpos, hrespos,
      hcommonlen, hressum⟩
  have hwis : ∀ i ∈ is, 0 < w i := by
    intro i hi
    exact hw i
  have hfpPos : ∀ z ∈ matched ++ residual, 0 < z := by
    intro z hz
    rw [List.mem_append] at hz
    exact hz.elim (hmatchedpos z) (hrespos z)
  rcases assemble_refinements is w p q hd (matched ++ residual) matched
      hxpRef hyqRef hwis hfpPos hmatchedpos with
    ⟨l, href0, hassembly, hlpos⟩
  have href : Refines g l := by
    simpa [is, w, m, List.map_get_finRange] using href0
  let halves := rem.map (· / 2)
  have hassembly' : l.Perm
      ((matched ++ residual) ++ matched ++ doubleList halves) := by
    rw [bisectPieces_eq_doubleList_map] at hassembly
    simpa [rem, halves] using hassembly
  have hpairedPerm : l.Perm (doubleList (matched ++ halves) ++ residual) :=
    hassembly'.trans (paired_assembly_perm matched residual halves)
  have hrempos : ∀ z ∈ rem, 0 < z := by
    simpa [rem, is] using remainingWeights_finRange_pos w hw p q
  have hhalvespos : ∀ z ∈ halves, 0 < z := by
    intro z hz
    simp only [halves, List.mem_map] at hz
    rcases hz with ⟨x, hx, rfl⟩
    linarith [hrempos x hx]
  have hpairedpos : ∀ z ∈ matched ++ halves, 0 < z := by
    intro z hz
    rw [List.mem_append] at hz
    exact hz.elim (hmatchedpos z) (hhalvespos z)
  have hpqcard : p.card + q.card ≤ m := by
    rw [← Finset.card_union_of_disjoint hd]
    simpa only [Fintype.card_fin] using Finset.card_le_univ (p ∪ q)
  have hremlen : rem.length = m - (p.card + q.card) := by
    simpa [rem, is] using remainingWeights_finRange_length w p q hd
  have hselectlens : xp.length + yq.length = p.card + q.card := by
    rw [show xp.length = p.card by
      simpa [xp, is] using selectWeights_finRange_length w p]
    rw [show yq.length = q.card by
      simpa [yq, is] using selectWeights_finRange_length w q]
  have hcommonlen' : 2 * matched.length + residual.length ≤
      2 * (p.card + q.card) - 1 := by
    rw [← hselectlens]
    exact hcommonlen
  have hlenEq := hpairedPerm.length_eq
  simp only [List.length_append, doubleList_length] at hlenEq
  have hhalveslen : halves.length = rem.length := by simp [halves]
  have hlenEq' : l.length =
      2 * matched.length + residual.length + 2 * rem.length := by
    rw [hhalveslen] at hlenEq
    omega
  have hpqpos : 0 < p.card + q.card := by
    have := Finset.card_pos.mpr hpne
    omega
  have hllen : l.length ≤ 2 * g.length - 1 := by
    dsimp [m] at hremlen hpqcard ⊢
    omega
  have hresbound : residual.sum ≤
      1 / ((2 ^ g.length - 1 : ℕ) : ℝ) := by
    rw [hressum, hxpsum, hyqsum]
    simpa [m] using hclose
  exact ⟨l, matched ++ halves, residual, href, hpairedPerm, hlpos,
    hpairedpos, hrespos, hllen, hresbound⟩

end FullCardinalityStrategy

end LiuBangXiangYuUpperScratch

lemma p3_denominator_pos (n : ℕ) :
    0 < (2 : ℝ) ^ (n + 1) - 1 := by
  have hp : (1 : ℝ) < 2 ^ (n + 1) :=
    one_lt_pow₀ (by norm_num) (by omega)
  linarith

lemma p3_half_add_error_eq_answer (n : ℕ) :
    (1 + 1 / ((2 : ℝ) ^ (n + 1) - 1)) / 2 =
      (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1) := by
  have hd : (2 : ℝ) ^ (n + 1) - 1 ≠ 0 := ne_of_gt (p3_denominator_pos n)
  field_simp [hd]
  rw [pow_succ]
  ring

lemma p3_half_le_answer (n : ℕ) :
    (1 : ℝ) / 2 ≤ (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1) := by
  rw [← p3_half_add_error_eq_answer]
  have hi : 0 ≤ 1 / ((2 : ℝ) ^ (n + 1) - 1) := by
    exact one_div_nonneg.mpr (p3_denominator_pos n).le
  linarith

lemma p3_nat_denominator_cast (k : ℕ) :
    (((2 ^ k - 1 : ℕ) : ℕ) : ℝ) = (2 : ℝ) ^ k - 1 := by
  have hpowpos : 0 < (2 : ℕ) ^ k := pow_pos (by omega) k
  rw [Nat.cast_sub (by omega : 1 ≤ 2 ^ k)]
  norm_num

lemma p3_bisectPieces_eq_pairDup_halves (l : List ℝ) :
    P3Realization.bisectPieces l = P3Agent.pairDup (l.map (· / 2)) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp [P3Realization.bisectPieces, P3Agent.pairDup] at ih ⊢
      exact ih

lemma realize_p3_refinement {A : Finset ℝ} {l : List ℝ}
    (href : P3Realization.Refines (pieceLengths A) l)
    (hlpos : ∀ z ∈ l, 0 < z) :
    ∃ B : Finset ℝ,
      Disjoint A B ∧ ↑B ⊆ Set.Ioo (0 : ℝ) 1 ∧
      pieceLengths (A ∪ B) = l ∧
      B.card = l.length - 1 - A.card := by
  let B := P3Realization.extraCuts A l
  have hsum : l.sum = 1 := by
    rw [href.sum_eq, pieceLengths_sum_all]
  have hAcut : A ⊆ P3Realization.cutFinset l := by
    rw [← P3Realization.cutFinset_pieceLengths A]
    exact href.cutFinset_subset
  have hne : l ≠ [] := by
    intro hnil
    rw [hnil] at hsum
    simp at hsum
  have hpiecesP3 : pieceLengths (A ∪ B) = l := by
    rw [P3Realization.union_extraCuts hAcut]
    exact P3Realization.pieceLengths_cutFinset l hne hlpos hsum
  have hpieces : pieceLengths (A ∪ B) = l := hpiecesP3
  refine ⟨B, P3Realization.extraCuts_disjoint A l,
    P3Realization.extraCuts_admissible hlpos hsum, hpieces, ?_⟩
  exact P3Realization.extraCuts_card hAcut hlpos

theorem upper_bound_aux (n : ℕ) (hn : 0 < n) :
    ∀ A : Finset ℝ, AdmissibleMark n A →
      ∃ B : Finset ℝ, AdmissibleMark n B ∧ Disjoint A B ∧
        L A B ≤ (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1) := by
  intro A hA
  by_cases hfull : A.card = n
  · let g : List ℝ := pieceLengths A
    have hgpos : ∀ z ∈ g, 0 < z := by
      exact pieceLengths_pos A hA.1
    have hgsum : g.sum = 1 := by
      exact pieceLengths_sum_all A
    have hglen : g.length = n + 1 := by
      dsimp [g]
      rw [pieceLengths_length, hfull]
    have hgne : g ≠ [] := by
      intro hnil
      rw [hnil] at hglen
      simp at hglen
    obtain ⟨l, paired, residual, hrefUpper, hperm, hlpos,
        hpairedpos, hrespos, hllen, hresbound⟩ :=
      LiuBangXiangYuUpperScratch.exists_paired_refinement g hgne hgpos hgsum
    have href : P3Realization.Refines (pieceLengths A) l := by
      exact hrefUpper
    obtain ⟨B, hdisjoint, hBint, hpieces, hBcard⟩ :=
      realize_p3_refinement href hlpos
    have hBcardle : B.card ≤ n := by
      omega
    refine ⟨B, ⟨hBint, hBcardle⟩, hdisjoint, ?_⟩
    have hlsum : l.sum = 1 := by
      rw [href.sum_eq, pieceLengths_sum_all]
    have hpermAgent : l.Perm (P3Agent.pairDup paired ++ residual) := by
      exact hperm
    have hsharele : firstPlayerShare l ≤ paired.sum + residual.sum := by
      exact P3Agent.firstPlayerShare_perm_pairDup_append_le_of_nonneg hpermAgent
        (fun z hz => (hpairedpos z hz).le) (fun z hz => (hrespos z hz).le)
    have hpairResidual :
        paired.sum + residual.sum = (1 + residual.sum) / 2 := by
      have hpermSum := hperm.sum_eq
      simp only [List.sum_append,
        LiuBangXiangYuUpperScratch.doubleList_sum] at hpermSum
      linarith
    have hresboundReal :
        residual.sum ≤ 1 / ((2 : ℝ) ^ (n + 1) - 1) := by
      rw [hglen, p3_nat_denominator_cast] at hresbound
      exact hresbound
    calc
      L A B = firstPlayerShare l := by rw [L, hpieces]
      _ ≤ paired.sum + residual.sum := hsharele
      _ = (1 + residual.sum) / 2 := hpairResidual
      _ ≤ (1 + 1 / ((2 : ℝ) ^ (n + 1) - 1)) / 2 := by linarith
      _ = (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1) :=
        p3_half_add_error_eq_answer n
  · have hcardlt : A.card < n := lt_of_le_of_ne hA.2 hfull
    let g : List ℝ := pieceLengths A
    let l : List ℝ := P3Realization.bisectPieces g
    have hgpos : ∀ z ∈ g, 0 < z := by
      exact pieceLengths_pos A hA.1
    have hlpos : ∀ z ∈ l, 0 < z := by
      exact P3Realization.bisectPieces_pos hgpos
    have href : P3Realization.Refines (pieceLengths A) l := by
      exact P3Realization.refines_bisectPieces g
    obtain ⟨B, hdisjoint, hBint, hpieces, hBcard⟩ :=
      realize_p3_refinement href hlpos
    have hglen : g.length = A.card + 1 := by
      exact pieceLengths_length A
    have hllen : l.length = 2 * g.length := by
      exact P3Realization.bisectPieces_length g
    have hBcardle : B.card ≤ n := by omega
    refine ⟨B, ⟨hBint, hBcardle⟩, hdisjoint, ?_⟩
    have hlsum : l.sum = 1 := by
      rw [P3Realization.bisectPieces_sum, pieceLengths_sum_all]
    have hpair : l.Perm (P3Agent.pairDup (g.map (· / 2))) := by
      exact List.Perm.of_eq (p3_bisectPieces_eq_pairDup_halves g)
    have hshare : firstPlayerShare l = (1 : ℝ) / 2 := by
      exact P3Agent.firstPlayerShare_half_of_perm_pairDup hpair hlsum
    calc
      L A B = firstPlayerShare l := by rw [L, hpieces]
      _ = (1 : ℝ) / 2 := hshare
      _ ≤ (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1) := p3_half_le_answer n

/-! ## Main Statements -/

/-- **Main statement.** For every positive integer `n`, Liu Bang's guaranteed
value equals `2^n / (2^(n+1) - 1)`. -/
theorem V_eq (n : ℕ) (hn : 0 < n) : V n = (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1) := by
  change V n = answer n
  exact V_eq_of_bounds n (by simpa [answer] using lower_bound_aux n hn)
    (by simpa [answer] using upper_bound_aux n hn)

/-- **Lower bound.** Liu Bang has an admissible marking `A` such that for every
admissible marking `B` disjoint from `A`, his guaranteed share is at least
`2^n / (2^(n+1) - 1)`. -/
theorem lower_bound (n : ℕ) (hn : 0 < n) :
    ∃ A : Finset ℝ, AdmissibleMark n A ∧
      ∀ B : Finset ℝ, AdmissibleMark n B → Disjoint A B →
        (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1) ≤ L A B := by
  exact lower_bound_aux n hn

/-- **Upper bound / optimality.** For every admissible marking `A` of Liu Bang,
Xiang Yu has an admissible marking `B` disjoint from `A` with
`L A B ≤ 2^n / (2^(n+1) - 1)`, so Liu Bang cannot guarantee more. -/
theorem upper_bound (n : ℕ) (hn : 0 < n) :
    ∀ A : Finset ℝ, AdmissibleMark n A →
      ∃ B : Finset ℝ, AdmissibleMark n B ∧ Disjoint A B ∧
        L A B ≤ (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1) := by
  exact upper_bound_aux n hn

end LiuBangXiangYu
