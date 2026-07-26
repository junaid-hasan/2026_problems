import Mathlib
set_option backward.isDefEq.respectTransparency false

/-- The subtype of positive real numbers, representing `\mathbb{R}_{>0}`. -/
abbrev PositiveReal : Type := {x : ℝ // 0 < x}

/-- The two-sided inequality defining admissible functions on positive real numbers. -/
def IsAdmissible (f : PositiveReal → PositiveReal) : Prop :=
  ∀ x y : PositiveReal,
    Real.sqrt (((x : ℝ) ^ 2 + (f y : ℝ) ^ 2) / 2) ≥
        ((f x : ℝ) + (y : ℝ)) / 2 ∧
      ((f x : ℝ) + (y : ℝ)) / 2 ≥
        Real.sqrt ((x : ℝ) * (f y : ℝ))

theorem main_theorem (f : PositiveReal → PositiveReal) :
    IsAdmissible f ↔
      ∃ c : ℝ, 0 ≤ c ∧ ∀ x : PositiveReal, (f x : ℝ) = (x : ℝ) + c := by
  constructor
  · intro h
    let d : PositiveReal → ℝ := fun x => (f x : ℝ) - (x : ℝ)
    have hsquares (x y : PositiveReal) :
        4 * (x : ℝ) * (f y : ℝ) ≤ ((f x : ℝ) + (y : ℝ)) ^ 2 ∧
          ((f x : ℝ) + (y : ℝ)) ^ 2 ≤
            2 * ((x : ℝ) ^ 2 + (f y : ℝ) ^ 2) := by
      rcases h x y with ⟨hu, hl⟩
      have hr₁ : 0 ≤ (((x : ℝ) ^ 2 + (f y : ℝ) ^ 2) / 2) := by
        nlinarith [sq_nonneg (x : ℝ), sq_nonneg (f y : ℝ)]
      have hr₂ : 0 ≤ (x : ℝ) * (f y : ℝ) :=
        mul_nonneg (le_of_lt x.property) (le_of_lt (f y).property)
      have hm : 0 < ((f x : ℝ) + (y : ℝ)) / 2 := by
        nlinarith [(f x).property, y.property]
      have hs₁ := Real.sq_sqrt hr₁
      have hs₂ := Real.sq_sqrt hr₂
      have hsn₁ := Real.sqrt_nonneg (((x : ℝ) ^ 2 + (f y : ℝ) ^ 2) / 2)
      have hsn₂ := Real.sqrt_nonneg ((x : ℝ) * (f y : ℝ))
      constructor <;> nlinarith
    have hgap (x y : PositiveReal) :
        |d x - d y| * (2 * (x : ℝ) + 2 * (y : ℝ) + d x + d y) ≤
          ((x : ℝ) - (y : ℝ) - d y) ^ 2 := by
      rcases hsquares x y with ⟨hl, hu⟩
      have hsum : 0 < 2 * (x : ℝ) + 2 * (y : ℝ) + d x + d y := by
        dsimp [d]
        nlinarith [(f x).property, (f y).property, x.property, y.property]
      have hlow :
          -(((x : ℝ) - (f y : ℝ)) ^ 2) ≤
            ((f x : ℝ) + (y : ℝ)) ^ 2 - ((x : ℝ) + (f y : ℝ)) ^ 2 := by
        nlinarith
      have hupp :
          ((f x : ℝ) + (y : ℝ)) ^ 2 - ((x : ℝ) + (f y : ℝ)) ^ 2 ≤
            ((x : ℝ) - (f y : ℝ)) ^ 2 := by
        nlinarith
      have habs :
          |((f x : ℝ) + (y : ℝ)) ^ 2 - ((x : ℝ) + (f y : ℝ)) ^ 2| ≤
            ((x : ℝ) - (f y : ℝ)) ^ 2 := abs_le.mpr ⟨hlow, hupp⟩
      rw [show ((f x : ℝ) + (y : ℝ)) ^ 2 - ((x : ℝ) + (f y : ℝ)) ^ 2 =
          (d x - d y) * (2 * (x : ℝ) + 2 * (y : ℝ) + d x + d y) by
            dsimp [d]; ring] at habs
      rw [abs_mul, abs_of_pos hsum] at habs
      convert habs using 1
      all_goals
        dsimp [d]
        ring
    have horbit (y : PositiveReal) :
        (f (f y) : ℝ) + (y : ℝ) = 2 * (f y : ℝ) := by
      have hy := h (f y) y
      have hp : 0 < (f y : ℝ) := (f y).property
      have hsqrtmul : Real.sqrt ((f y : ℝ) * (f y : ℝ)) = (f y : ℝ) := by
        rw [show (f y : ℝ) * (f y : ℝ) = (f y : ℝ) ^ 2 by ring,
          Real.sqrt_sq_eq_abs, abs_of_pos hp]
      norm_num [Real.sqrt_sq_eq_abs, abs_of_pos hp, hsqrtmul] at hy
      nlinarith
    have hdinv (y : PositiveReal) : d (f y) = d y := by
      dsimp [d]
      nlinarith [horbit y]
    have hiter_disp (x : PositiveReal) :
        ∀ n : ℕ, d ((f^[n]) x) = d x := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [Function.iterate_succ_apply', hdinv, ih]
    have hstep (z : PositiveReal) : (f z : ℝ) = (z : ℝ) + d z := by
      dsimp [d]
      ring
    have hiter_val (x : PositiveReal) :
        ∀ n : ℕ, (((f^[n]) x : PositiveReal) : ℝ) =
          (x : ℝ) + (n : ℝ) * d x := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [Function.iterate_succ_apply', hstep, hiter_disp, ih]
          push_cast
          ring
    have hd_nonneg (x : PositiveReal) : 0 ≤ d x := by
      by_contra hn
      have hdneg : d x < 0 := lt_of_not_ge hn
      obtain ⟨n : ℕ, hn⟩ := exists_nat_gt ((x : ℝ) / (-d x))
      have hden : 0 < -d x := neg_pos.mpr hdneg
      have hmul : (x : ℝ) < (n : ℝ) * (-d x) :=
        (div_lt_iff₀ hden).mp hn
      have hp := (((f^[n]) x : PositiveReal).property)
      rw [hiter_val] at hp
      nlinarith
    have hd_pos_eq (x y : PositiveReal) (hx : 0 < d x) (hy : 0 < d y) :
        d x = d y := by
      by_contra hxy
      have hdelta : 0 < |d x - d y| := by
        apply abs_pos.mpr
        intro hz
        apply hxy
        linarith
      have hden₁ : 0 < 2 * |d x - d y| * d y := by positivity
      obtain ⟨m : ℕ, hm⟩ := exists_nat_gt
        (max ((d x) ^ 2 / (2 * |d x - d y| * d y))
          (((x : ℝ) - (y : ℝ)) / d y))
      have hm₁ : (d x) ^ 2 / (2 * |d x - d y| * d y) < (m : ℝ) :=
        lt_of_le_of_lt (le_max_left _ _) hm
      have hm₂ : ((x : ℝ) - (y : ℝ)) / d y < (m : ℝ) :=
        lt_of_le_of_lt (le_max_right _ _) hm
      have hmul₁ : (d x) ^ 2 < (m : ℝ) * (2 * |d x - d y| * d y) :=
        (div_lt_iff₀ hden₁).mp hm₁
      have hlarge :
          (d x) ^ 2 < |d x - d y| *
            (2 * ((y : ℝ) + (m : ℝ) * d y)) := by
        calc
          (d x) ^ 2 < (m : ℝ) * (2 * |d x - d y| * d y) := hmul₁
          _ = |d x - d y| * (2 * ((m : ℝ) * d y)) := by ring
          _ < |d x - d y| * (2 * ((y : ℝ) + (m : ℝ) * d y)) := by
            gcongr
            linarith [y.property]
      have hmul₂ : (x : ℝ) - (y : ℝ) < (m : ℝ) * d y :=
        (div_lt_iff₀ hy).mp hm₂
      have htarget :
          (x : ℝ) < (y : ℝ) + ((m : ℝ) + 1) * d y := by
        nlinarith
      let target : ℝ := (y : ℝ) + ((m : ℝ) + 1) * d y
      obtain ⟨N : ℕ, hN⟩ := exists_nat_gt ((target - (x : ℝ)) / d x)
      have hNcross : target ≤ (x : ℝ) + (N : ℝ) * d x := by
        have := (div_lt_iff₀ hx).mp hN
        linarith
      have hex : ∃ n : ℕ, target ≤ (x : ℝ) + (n : ℝ) * d x := ⟨N, hNcross⟩
      let n : ℕ := Nat.find hex
      have hncross : target ≤ (x : ℝ) + (n : ℝ) * d x := by
        exact Nat.find_spec hex
      have hnpos : 0 < n := by
        by_contra hn
        have hnzero : n = 0 := by omega
        rw [hnzero] at hncross
        norm_num at hncross
        dsimp [target] at hncross
        linarith
      obtain ⟨k : ℕ, hk⟩ : ∃ k : ℕ, n = k + 1 := by
        exact ⟨n - 1, by omega⟩
      have hklt : k < Nat.find hex := by
        change k < n
        omega
      have hknot : ¬target ≤ (x : ℝ) + (k : ℝ) * d x :=
        Nat.find_min hex hklt
      have hkbelow : (x : ℝ) + (k : ℝ) * d x < target := lt_of_not_ge hknot
      have hclose₀ : 0 ≤ (x : ℝ) + (n : ℝ) * d x - target := by linarith
      have hclose₁ : (x : ℝ) + (n : ℝ) * d x - target < d x := by
        rw [hk]
        push_cast
        nlinarith
      have hsmall :
          ((x : ℝ) + (n : ℝ) * d x - target) ^ 2 < (d x) ^ 2 := by
        nlinarith [sq_nonneg ((x : ℝ) + (n : ℝ) * d x - target)]
      have hg := hgap ((f^[n]) x) ((f^[m]) y)
      rw [hiter_disp x n, hiter_disp y m, hiter_val x n, hiter_val y m] at hg
      have hxiter : 0 < (x : ℝ) + (n : ℝ) * d x := by
        rw [← hiter_val x n]
        exact ((f^[n]) x).property
      have hfactor :
          2 * ((y : ℝ) + (m : ℝ) * d y) <
            2 * ((x : ℝ) + (n : ℝ) * d x) +
              2 * ((y : ℝ) + (m : ℝ) * d y) + d x + d y := by
        nlinarith
      have hleft :
          (d x) ^ 2 < |d x - d y| *
            (2 * ((x : ℝ) + (n : ℝ) * d x) +
              2 * ((y : ℝ) + (m : ℝ) * d y) + d x + d y) :=
        lt_trans hlarge (mul_lt_mul_of_pos_left hfactor hdelta)
      dsimp [target] at hsmall
      nlinarith
    have hno_mix (x y : PositiveReal) (hx : 0 < d x) (hy : d y = 0) : False := by
      have hd_cases (z : PositiveReal) : d z = 0 ∨ d z = d x := by
        by_cases hz : d z = 0
        · exact Or.inl hz
        · right
          apply hd_pos_eq z x
          · exact lt_of_le_of_ne (hd_nonneg z) (Ne.symm hz)
          · exact hx
      have hsep (u v : PositiveReal) (hu : 0 < d u) (hv : d v = 0) :
          d u < dist u v := by
        have hg := hgap u v
        simp only [hv, sub_zero, add_zero, abs_of_pos hu] at hg
        have hsq : (d u) ^ 2 < ((u : ℝ) - (v : ℝ)) ^ 2 := by
          nlinarith [u.property, v.property]
        have ha := abs_nonneg ((u : ℝ) - (v : ℝ))
        have hasq := sq_abs ((u : ℝ) - (v : ℝ))
        have halt : d u < |(u : ℝ) - (v : ℝ)| := by nlinarith
        rw [Subtype.dist_eq, Real.dist_eq]
        exact halt
      have hd_cont : Continuous d := continuous_iff_continuousAt.mpr fun z => by
        refine (continuousAt_const (x := z) (y := d z)).congr_of_eventuallyEq ?_
        filter_upwards [Metric.ball_mem_nhds z hx] with w hw
        rw [Metric.mem_ball] at hw
        rcases hd_cases z with hz | hz <;> rcases hd_cases w with hw₀ | hw₀
        · rw [hz, hw₀]
        · have hwp : 0 < d w := by rw [hw₀]; exact hx
          have hs := hsep w z hwp hz
          rw [hw₀] at hs
          linarith
        · have hzp : 0 < d z := by rw [hz]; exact hx
          have hs := hsep z w hzp hw₀
          rw [hz, dist_comm] at hs
          linarith
        · rw [hz, hw₀]
      have hmid : ∃ z : PositiveReal, d z = d x / 2 := by
        letI : PreconnectedSpace PositiveReal :=
          Subtype.preconnectedSpace (isPreconnected_Ioi :
            IsPreconnected (Set.Ioi (0 : ℝ)))
        have hmemb : d x / 2 ∈ Set.Icc (d y) (d x) := by
          rw [hy]
          constructor <;> nlinarith
        have himage := isPreconnected_univ.intermediate_value
          (a := y) (b := x) (by simp) (by simp) hd_cont.continuousOn hmemb
        rcases himage with ⟨z, -, hz⟩
        exact ⟨z, hz⟩
      rcases hmid with ⟨z, hz⟩
      have hzp : 0 < d z := by rw [hz]; nlinarith
      have heq := hd_pos_eq z x hzp hx
      rw [hz] at heq
      nlinarith
    have hd_all (x y : PositiveReal) : d x = d y := by
      by_cases hx : d x = 0
      · by_cases hy : d y = 0
        · rw [hx, hy]
        · have hyp : 0 < d y := lt_of_le_of_ne (hd_nonneg y) (Ne.symm hy)
          exact (hno_mix y x hyp hx).elim
      · have hxp : 0 < d x := lt_of_le_of_ne (hd_nonneg x) (Ne.symm hx)
        by_cases hy : d y = 0
        · exact (hno_mix x y hxp hy).elim
        · have hyp : 0 < d y := lt_of_le_of_ne (hd_nonneg y) (Ne.symm hy)
          exact hd_pos_eq x y hxp hyp
    clear horbit
    exact ⟨d (⟨1, by norm_num⟩ : PositiveReal), hd_nonneg _, fun x => by
      rw [hstep]
      rw [hd_all x (⟨1, by norm_num⟩ : PositiveReal)]⟩
  · rintro ⟨c, hc, hf⟩
    intro x y
    rw [hf x, hf y]
    constructor
    · have hr : 0 ≤ (((x : ℝ) ^ 2 + ((y : ℝ) + c) ^ 2) / 2) := by positivity
      have hs := Real.sq_sqrt hr
      have hsn := Real.sqrt_nonneg (((x : ℝ) ^ 2 + ((y : ℝ) + c) ^ 2) / 2)
      have hm : 0 < (((x : ℝ) + c) + (y : ℝ)) / 2 := by
        nlinarith [x.property, y.property]
      nlinarith [sq_nonneg ((x : ℝ) - (y : ℝ) - c)]

    · have hyc : 0 ≤ (y : ℝ) + c := by nlinarith [y.property]
      have hr : 0 ≤ (x : ℝ) * ((y : ℝ) + c) :=
        mul_nonneg (le_of_lt x.property) hyc
      have hs := Real.sq_sqrt hr
      have hsn := Real.sqrt_nonneg ((x : ℝ) * ((y : ℝ) + c))
      have hm : 0 < (((x : ℝ) + c) + (y : ℝ)) / 2 := by
        nlinarith [x.property, y.property]
      nlinarith [sq_nonneg ((x : ℝ) - (y : ℝ) - c)]
