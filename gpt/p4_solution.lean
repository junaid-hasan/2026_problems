import Mathlib
set_option backward.isDefEq.respectTransparency false

namespace TriangleGame

/-- A triangle, viewed as the multiset of its three interior angles (in degrees):
positive reals summing to `180`. -/
def IsTriangle (s : Multiset ℝ) : Prop :=
  s.card = 3 ∧ (∀ x ∈ s, 0 < x) ∧ s.sum = 180

/-- A triangle `s` has an interior angle equal to `θ`. -/
def HasAngle (θ : ℝ) (s : Multiset ℝ) : Prop := θ ∈ s

/-- One admissible cut of the triangle `s`, producing children `L` and `R`.

We pick an apex angle `α` and the two base angles `β, γ` (so `s = {α, β, γ}`), and a
cut parameter `x` in the open interval `(γ, 180 - β)`. The resulting two triangles
have angle multisets `L = {β, x, 180 - β - x}` and `R = {γ, 180 - x, x - γ}`.
Ranging over all `α, β, γ` with `s = {α, β, γ}` captures all three apex choices and
both assignments of the two base angles. -/
def IsCut (s L R : Multiset ℝ) : Prop :=
  ∃ α β γ x : ℝ,
    s = {α, β, γ} ∧ γ < x ∧ x < 180 - β ∧
      L = {β, x, 180 - β - x} ∧ R = {γ, 180 - x, x - γ}

/-- The set of triangles from which Mulan can force, in finitely many steps, a
triangle with an interior angle equal to `θ`, no matter how Shan-Yu discards.

This is the least predicate closed under:
* (`win`) if the current triangle already has an angle equal to `θ`, Mulan has won;
* (`move`) if Mulan can make a cut producing children `L` and `R` from *both* of
  which she wins (so whichever one Shan-Yu keeps, she still wins), then she wins
  from the current triangle.

Membership means Mulan wins in finitely many steps. -/
inductive MulanWins (θ : ℝ) : Multiset ℝ → Prop
  | win {s : Multiset ℝ} (h : HasAngle θ s) : MulanWins θ s
  | move {s L R : Multiset ℝ} (hcut : IsCut s L R)
      (hL : MulanWins θ L) (hR : MulanWins θ R) : MulanWins θ s

/-- Mulan can guarantee victory for the value `θ`: from every valid starting
triangle she wins in finitely many steps regardless of Shan-Yu's play. -/
def MulanCanGuarantee (θ : ℝ) : Prop :=
  ∀ s : Multiset ℝ, IsTriangle s → MulanWins θ s

lemma mulanWins_of_nat_mul_angle (θ : ℝ) (hθ : 0 < θ) :
    ∀ k : ℕ, 1 ≤ k → ∀ s : Multiset ℝ, IsTriangle s →
      (k : ℝ) * θ ∈ s → MulanWins θ s := by
  intro k
  induction k with
  | zero => omega
  | succ k ih =>
      intro hk s hs hmem
      by_cases hk0 : k = 0
      · subst k
        apply MulanWins.win
        simpa [HasAngle] using hmem
      · have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
        obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hmem
        have htcard : t.card = 2 := by
          simpa using hs.1
        obtain ⟨β, γ, rfl⟩ := Multiset.card_eq_two.mp htcard
        have hmul : 0 < ((k + 1 : ℕ) : ℝ) * θ := hs.2.1 _ (by simp)
        have hβ : 0 < β := hs.2.1 _ (by simp)
        have hγ : 0 < γ := hs.2.1 _ (by simp)
        have hsum : ((k + 1 : ℕ) : ℝ) * θ + β + γ = 180 := by
          simpa [add_assoc] using hs.2.2
        let L : Multiset ℝ := {β, γ + θ, (k : ℝ) * θ}
        let R : Multiset ℝ := {γ, 180 - (γ + θ), θ}
        have hLtri : IsTriangle L := by
          refine ⟨by simp [L], ?_, ?_⟩
          · intro y hy
            have hy' : y = β ∨ y = γ + θ ∨ y = (k : ℝ) * θ := by
              simpa [L] using hy
            rcases hy' with hy | hy | hy
            · subst y
              exact hβ
            · subst y
              positivity
            · subst y
              positivity
          · simp only [L]
            norm_num [Nat.cast_add, Nat.cast_one] at hsum ⊢
            linarith
        have hLmem : (k : ℝ) * θ ∈ L := by simp [L]
        have hLwin : MulanWins θ L := ih hkpos L hLtri hLmem
        have hRwin : MulanWins θ R := by
          apply MulanWins.win
          simp [HasAngle, R]
        apply MulanWins.move (L := L) (R := R)
        · refine ⟨((k + 1 : ℕ) : ℝ) * θ, β, γ, γ + θ, rfl,
            by linarith, ?_, ?_, ?_⟩
          · have hkθ : 0 < (k : ℝ) * θ := by positivity
            norm_num [Nat.cast_add, Nat.cast_one] at hsum ⊢
            linarith
          · simp only [L]
            have heq : 180 - β - (γ + θ) = (k : ℝ) * θ := by
              norm_num [Nat.cast_add, Nat.cast_one] at hsum
              linarith
            rw [heq]
          · simp only [R]
            rw [show γ + θ - γ = θ by ring]
        · exact hLwin
        · exact hRwin

lemma mulanWins_of_small_explicit (θ : ℝ) (n : ℕ)
    (hθ : 0 < θ) (hn : 2 ≤ n) (htotal : (n : ℝ) * θ = 180)
    (α β a : ℝ) (_hα : 0 < α) (hβ : 0 < β) (ha : 0 < a)
    (_hsum : α + β + a = 180) (haθ : a < θ) (hβbound : β < 180 - θ) :
    MulanWins θ {α, β, a} := by
  let L : Multiset ℝ := {β, θ, 180 - β - θ}
  let R : Multiset ℝ := {a, 180 - θ, θ - a}
  have hθ90 : θ ≤ 90 := by
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith [mul_nonneg (sub_nonneg.mpr hnR) (le_of_lt hθ)]
  have hRtri : IsTriangle R := by
    refine ⟨by simp [R], ?_, ?_⟩
    · intro y hy
      have hy' : y = a ∨ y = 180 - θ ∨ y = θ - a := by
        simpa [R] using hy
      rcases hy' with hy | hy | hy
      · subst y
        exact ha
      · subst y
        linarith
      · subst y
        linarith
    · simp [R]
  have hnsub : 1 ≤ n - 1 := by omega
  have hn1 : 1 ≤ n := by omega
  have hmulEq : ((n - 1 : ℕ) : ℝ) * θ = 180 - θ := by
    norm_num [Nat.cast_sub hn1] at htotal ⊢
    linarith
  have hRmem : ((n - 1 : ℕ) : ℝ) * θ ∈ R := by
    rw [hmulEq]
    simp [R]
  have hRwin : MulanWins θ R :=
    mulanWins_of_nat_mul_angle θ hθ (n - 1) hnsub R hRtri hRmem
  have hLwin : MulanWins θ L := by
    apply MulanWins.win
    simp [HasAngle, L]
  apply MulanWins.move (L := L) (R := R)
  · exact ⟨α, β, a, θ, rfl, haθ, by linarith, rfl, rfl⟩
  · exact hLwin
  · exact hRwin

lemma mulanWins_of_small_angle (θ : ℝ) (n : ℕ)
    (hθ : 0 < θ) (hn : 2 ≤ n) (htotal : (n : ℝ) * θ = 180)
    (s : Multiset ℝ) (hs : IsTriangle s) (a : ℝ) (hamem : a ∈ s)
    (ha : 0 < a) (haθ : a < θ) : MulanWins θ s := by
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hamem
  have htcard : t.card = 2 := by simpa using hs.1
  obtain ⟨b, c, rfl⟩ := Multiset.card_eq_two.mp htcard
  have hb : 0 < b := hs.2.1 _ (by simp)
  have hc : 0 < c := hs.2.1 _ (by simp)
  have hsum : a + b + c = 180 := by simpa [add_assoc] using hs.2.2
  have hθ90 : θ ≤ 90 := by
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith [mul_nonneg (sub_nonneg.mpr hnR) (le_of_lt hθ)]
  by_cases hbcut : b < 180 - θ
  · have hw := mulanWins_of_small_explicit θ n hθ hn htotal c b a hc hb ha
        (by linarith) haθ hbcut
    have heq : ({a, b, c} : Multiset ℝ) = {c, b, a} := by
      calc
        {a, b, c} = a ::ₘ c ::ₘ {b} :=
          congrArg (fun t : Multiset ℝ => a ::ₘ t) (Multiset.cons_swap b c 0)
        _ = c ::ₘ a ::ₘ {b} := Multiset.cons_swap a c {b}
        _ = {c, b, a} :=
          congrArg (fun t : Multiset ℝ => c ::ₘ t) (Multiset.cons_swap a b 0)
    change MulanWins θ ({a, b, c} : Multiset ℝ)
    rw [heq]
    exact hw
  · have hccut : c < 180 - θ := by
      have hbge : 180 - θ ≤ b := le_of_not_gt hbcut
      linarith
    have hw := mulanWins_of_small_explicit θ n hθ hn htotal b c a hb hc ha
        (by linarith) haθ hccut
    have heq : ({a, b, c} : Multiset ℝ) = {b, c, a} := by
      calc
        {a, b, c} = b ::ₘ a ::ₘ {c} := Multiset.cons_swap a b {c}
        _ = {b, c, a} :=
          congrArg (fun t : Multiset ℝ => b ::ₘ t) (Multiset.cons_swap a c 0)
    change MulanWins θ ({a, b, c} : Multiset ℝ)
    rw [heq]
    exact hw

lemma mulanCanGuarantee_of_nat_total (θ : ℝ) (n : ℕ)
    (hθ : 0 < θ) (hn : 2 ≤ n) (htotal : (n : ℝ) * θ = 180) :
    MulanCanGuarantee θ := by
  intro s hs
  obtain ⟨α, β, γ, rfl⟩ := Multiset.card_eq_three.mp hs.1
  have hα : 0 < α := hs.2.1 _ (by simp)
  have hβ : 0 < β := hs.2.1 _ (by simp)
  have hγ : 0 < γ := hs.2.1 _ (by simp)
  have hsum : α + β + γ = 180 := by simpa [add_assoc] using hs.2.2
  by_cases htarget : θ ∈ ({α, β, γ} : Multiset ℝ)
  · exact MulanWins.win htarget
  by_cases hsmall : ∃ a ∈ ({α, β, γ} : Multiset ℝ), a < θ
  · obtain ⟨a, hamem, haθ⟩ := hsmall
    exact mulanWins_of_small_angle θ n hθ hn htotal _ hs a hamem
      (hs.2.1 a hamem) haθ
  have hθα : θ < α := by
    have hle : θ ≤ α := by
      by_contra hnot
      exact hsmall ⟨α, by simp, lt_of_not_ge hnot⟩
    have hne : θ ≠ α := by
      intro heq
      apply htarget
      simp [heq]
    exact lt_of_le_of_ne hle hne
  let k : ℕ := ⌊α / θ⌋₊
  let δ : ℝ := (k : ℝ) * θ
  have hratio : 1 < α / θ := by
    apply (lt_div_iff₀ hθ).2
    simpa using hθα
  have hk : 1 ≤ k := by
    apply Nat.le_floor
    norm_num
    exact le_of_lt hratio
  have hfloorle : (k : ℝ) ≤ α / θ := by
    exact Nat.floor_le (by positivity)
  have hδpos : 0 < δ := by
    dsimp [δ]
    positivity
  have hδle : δ ≤ α := by
    dsimp [δ]
    calc
      (k : ℝ) * θ ≤ (α / θ) * θ :=
        mul_le_mul_of_nonneg_right hfloorle (le_of_lt hθ)
      _ = α := by field_simp
  by_cases hδeq : δ = α
  · apply mulanWins_of_nat_mul_angle θ hθ k hk _ hs
    simp [δ, hδeq]
  have hδlt : δ < α := lt_of_le_of_ne hδle hδeq
  have hratioUpper : α / θ < (k : ℝ) + 1 := Nat.lt_floor_add_one (α / θ)
  have hscaledUpper := mul_lt_mul_of_pos_right hratioUpper hθ
  have hreslt : α - δ < θ := by
    dsimp [δ] at hscaledUpper ⊢
    rw [div_mul_cancel₀ α (ne_of_gt hθ)] at hscaledUpper
    linarith
  have hrespos : 0 < α - δ := sub_pos.mpr hδlt
  let L : Multiset ℝ := {β, γ + δ, α - δ}
  let R : Multiset ℝ := {γ, 180 - (γ + δ), δ}
  have hLtri : IsTriangle L := by
    refine ⟨by simp [L], ?_, ?_⟩
    · intro y hy
      have hy' : y = β ∨ y = γ + δ ∨ y = α - δ := by
        simpa [L] using hy
      rcases hy' with hy | hy | hy
      · subst y
        exact hβ
      · subst y
        positivity
      · subst y
        exact hrespos
    · simp [L]
      linarith
  have hRtri : IsTriangle R := by
    refine ⟨by simp [R], ?_, ?_⟩
    · intro y hy
      have hy' : y = γ ∨ y = 180 - (γ + δ) ∨ y = δ := by
        simpa [R] using hy
      rcases hy' with hy | hy | hy
      · subst y
        exact hγ
      · subst y
        linarith
      · subst y
        exact hδpos
    · simp [R]
      ring
  have hLwin : MulanWins θ L :=
    mulanWins_of_small_angle θ n hθ hn htotal L hLtri (α - δ)
      (by simp [L]) hrespos hreslt
  have hRwin : MulanWins θ R :=
    mulanWins_of_nat_mul_angle θ hθ k hk R hRtri (by simp [R, δ])
  apply MulanWins.move (L := L) (R := R)
  · refine ⟨α, β, γ, γ + δ, rfl, by linarith, by linarith, ?_, ?_⟩
    · simp only [L]
      rw [show 180 - β - (γ + δ) = α - δ by linarith]
    · simp only [R]
      rw [show γ + δ - γ = δ by ring]
  · exact hLwin
  · exact hRwin

def IsIntMultiple (θ x : ℝ) : Prop := ∃ z : ℤ, x = (z : ℝ) * θ

lemma isIntMultiple_add {θ x y : ℝ} (hx : IsIntMultiple θ x)
    (hy : IsIntMultiple θ y) : IsIntMultiple θ (x + y) := by
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨n, rfl⟩ := hy
  refine ⟨m + n, ?_⟩
  push_cast
  ring

lemma isIntMultiple_sub {θ x y : ℝ} (hx : IsIntMultiple θ x)
    (hy : IsIntMultiple θ y) : IsIntMultiple θ (x - y) := by
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨n, rfl⟩ := hy
  refine ⟨m - n, ?_⟩
  push_cast
  ring

lemma mulanWins_forces_int_multiple (θ : ℝ) {s : Multiset ℝ}
    (hsum : s.sum = 180) (hw : MulanWins θ s) :
    IsIntMultiple θ 180 ∨ ∃ a ∈ s, IsIntMultiple θ a := by
  revert hsum
  induction hw with
  | win h =>
      intro _
      right
      exact ⟨θ, h, ⟨1, by norm_num⟩⟩
  | @move s L R hcut hL hR ihL ihR =>
      intro hsum
      obtain ⟨α, β, γ, x, hs, hγx, hxβ, hLdef, hRdef⟩ := hcut
      have hrootsum : α + β + γ = 180 := by
        rw [hs] at hsum
        simpa [add_assoc] using hsum
      have hLsum : L.sum = 180 := by
        rw [hLdef]
        simp
      have hRsum : R.sum = 180 := by
        rw [hRdef]
        simp
      rcases ihL hLsum with h180 | ⟨a, haL, haMul⟩
      · exact Or.inl h180
      rcases ihR hRsum with h180 | ⟨b, hbR, hbMul⟩
      · exact Or.inl h180
      have haCases : a = β ∨ a = x ∨ a = 180 - β - x := by
        rw [hLdef] at haL
        simpa using haL
      have hbCases : b = γ ∨ b = 180 - x ∨ b = x - γ := by
        rw [hRdef] at hbR
        simpa using hbR
      rcases haCases with ha | ha | ha
      · subst a
        right
        exact ⟨β, by rw [hs]; simp, haMul⟩
      · subst a
        rcases hbCases with hb | hb | hb
        · subst b
          right
          exact ⟨γ, by rw [hs]; simp, hbMul⟩
        · subst b
          left
          have h := isIntMultiple_add haMul hbMul
          convert h using 1
          all_goals ring
        · subst b
          right
          refine ⟨γ, by rw [hs]; simp, ?_⟩
          have h := isIntMultiple_sub haMul hbMul
          convert h using 1
          all_goals ring
      · subst a
        rcases hbCases with hb | hb | hb
        · subst b
          right
          exact ⟨γ, by rw [hs]; simp, hbMul⟩
        · subst b
          right
          refine ⟨β, by rw [hs]; simp, ?_⟩
          have h := isIntMultiple_sub hbMul haMul
          convert h using 1
          all_goals ring
        · subst b
          right
          refine ⟨α, by rw [hs]; simp, ?_⟩
          have h := isIntMultiple_add haMul hbMul
          have heq : (180 - β - x) + (x - γ) = α := by linarith
          rw [← heq]
          exact h

lemma guarantee_forces_nat_total (θ : ℝ) (hθ : 0 < θ) (hθ180 : θ < 180)
    (hguar : MulanCanGuarantee θ) :
    ∃ n : ℕ, 2 ≤ n ∧ θ = 180 / n := by
  let s : Multiset ℝ := {60, 60, 60}
  have hs : IsTriangle s := by
    norm_num [IsTriangle, s]
  have hw : MulanWins θ s := hguar s hs
  have hsum : s.sum = 180 := hs.2.2
  have hmultiple := mulanWins_forces_int_multiple θ hsum hw
  have h180multiple : IsIntMultiple θ 180 := by
    rcases hmultiple with h180 | ⟨a, ha, haMul⟩
    · exact h180
    · have haeq : a = 60 := by
        simpa [s] using ha
      subst a
      have h120 := isIntMultiple_add haMul haMul
      have h180 := isIntMultiple_add h120 haMul
      norm_num at h180 ⊢
      exact h180
  obtain ⟨z, hz⟩ := h180multiple
  have hzposR : 0 < (z : ℝ) := by
    have hprod : 0 < (z : ℝ) * θ := by rw [← hz]; norm_num
    rcases (mul_pos_iff.mp hprod) with h | h
    · exact h.1
    · linarith
  have hzgtR : 1 < (z : ℝ) := by
    by_contra hnot
    have hzle : (z : ℝ) ≤ 1 := le_of_not_gt hnot
    have hmulle := mul_le_mul_of_nonneg_right hzle (le_of_lt hθ)
    rw [← hz] at hmulle
    norm_num at hmulle
    linarith
  have hzgt : (1 : ℤ) < z := by exact_mod_cast hzgtR
  have hznonneg : (0 : ℤ) ≤ z := by omega
  have htoNat : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hznonneg
  have hn : 2 ≤ z.toNat := by omega
  have hcast : (z.toNat : ℝ) = (z : ℝ) := by
    exact_mod_cast htoNat
  refine ⟨z.toNat, hn, ?_⟩
  apply (eq_div_iff (by positivity : (z.toNat : ℝ) ≠ 0)).2
  rw [mul_comm, hcast]
  exact hz.symm

/-- **Main theorem.** For `0 < θ < 180`, Mulan can guarantee her victory in finitely
many steps, no matter how Shan-Yu plays, if and only if `θ = 180 / n` for some
integer `n ≥ 2`. -/
theorem main_theorem (θ : ℝ) (hθ0 : 0 < θ) (hθ180 : θ < 180) :
    MulanCanGuarantee θ ↔ ∃ n : ℕ, 2 ≤ n ∧ θ = 180 / n := by
  constructor
  · exact guarantee_forces_nat_total θ hθ0 hθ180
  · rintro ⟨n, hn, hθeq⟩
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have htotal : (n : ℝ) * θ = 180 := by
      rw [hθeq]
      field_simp
    exact mulanCanGuarantee_of_nat_total θ n hθ0 hn htotal

end TriangleGame
