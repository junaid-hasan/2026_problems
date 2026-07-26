import Mathlib
set_option backward.isDefEq.respectTransparency false

open EuclideanGeometry

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def cross (u v : Plane) : ℝ := u 0 * v 1 - u 1 * v 0

lemma cross_linear_combination (b c : Plane) (r s t u : ℝ) :
    cross (r • b + s • c) (t • b + u • c) =
      (r * u - s * t) * cross b c := by
  simp [cross]
  ring

lemma coefficients_eq_of_cross_ne {b c : Plane} {r s t u : ℝ}
    (hD : cross b c ≠ 0)
    (h : r • b + s • c = t • b + u • c) : r = t ∧ s = u := by
  have h₁ := congrArg (fun z => cross z c) h
  have h₂ := congrArg (fun z => cross b z) h
  simp [cross] at h₁ h₂
  have hrprod : (r - t) * cross b c = 0 := by
    unfold cross
    linear_combination h₁
  have hsprod : (s - u) * cross b c = 0 := by
    unfold cross
    linear_combination h₂
  constructor
  · exact sub_eq_zero.mp ((mul_eq_zero.mp hrprod).resolve_right hD)
  · exact sub_eq_zero.mp ((mul_eq_zero.mp hsprod).resolve_right hD)

lemma cross_sub_ne_zero_of_not_collinear {A B C : Plane}
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane)) :
    cross (B - A) (C - A) ≠ 0 := by
  intro hcross
  have hbne : B - A ≠ 0 := sub_ne_zero.mpr (ne₁₂_of_not_collinear hABC).symm
  let b : Plane := B - A
  let c : Plane := C - A
  have hbcross : b 0 * c 1 - b 1 * c 0 = 0 := by simpa [cross, b, c] using hcross
  obtain ⟨r, hcr⟩ : ∃ r : ℝ, c = r • b := by
    by_cases hb0 : b 0 = 0
    · have hb1 : b 1 ≠ 0 := by
        intro hb1
        apply hbne
        ext i
        fin_cases i <;> simp [b, hb0, hb1]
      refine ⟨c 1 / b 1, ?_⟩
      ext i
      fin_cases i
      · have hprod : b 1 * c 0 = 0 := by
          rw [hb0, zero_mul, zero_sub, neg_eq_zero] at hbcross
          exact hbcross
        have hc0 : c 0 = 0 := (mul_eq_zero.mp hprod).resolve_left hb1
        simp [hb0, hc0]
      · simp
        field_simp
    · refine ⟨c 0 / b 0, ?_⟩
      ext i
      fin_cases i
      · simp
        field_simp
      · simp
        field_simp
        nlinarith
  apply hABC
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨A, B - A, ?_⟩
  intro P hP
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP
  rcases hP with hP | hP | hP
  · subst P
    exact ⟨0, by simp⟩
  · subst P
    exact ⟨1, by simp⟩
  · subst P
    refine ⟨r, ?_⟩
    change C = r • (B - A) + A
    rw [← hcr]
    simp [c]

lemma gram_det_eq_cross_sq (u v : Plane) :
    inner ℝ u u * inner ℝ v v - inner ℝ u v * inner ℝ u v = cross u v ^ 2 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two]
  simp
  simp [cross]
  ring

lemma sin_angle_mul_norms_eq_abs_cross (u v : Plane) :
    Real.sin (InnerProductGeometry.angle u v) * (‖u‖ * ‖v‖) = |cross u v| := by
  rw [InnerProductGeometry.sin_angle_mul_norm_mul_norm]
  rw [gram_det_eq_cross_sq, Real.sqrt_sq_eq_abs]

lemma cos_angle_mul_norms_eq_inner {u v : Plane} (hcross : cross u v ≠ 0) :
    Real.cos (InnerProductGeometry.angle u v) * (‖u‖ * ‖v‖) = inner ℝ u v := by
  have hu : u ≠ 0 := by
    intro hu
    subst u
    simp [cross] at hcross
  have hv : v ≠ 0 := by
    intro hv
    subst v
    simp [cross] at hcross
  rw [InnerProductGeometry.cos_angle]
  field_simp

lemma coeff_inner_relation_of_angle_eq
    (u v w z : Plane) (d₁ d₂ D : ℝ)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hD : D ≠ 0)
    (huv : cross u v = d₁ * D) (hwz : cross w z = d₂ * D)
    (hang : InnerProductGeometry.angle u v = InnerProductGeometry.angle w z) :
    d₁ * inner ℝ w z = d₂ * inner ℝ u v := by
  have huv0 : cross u v ≠ 0 := by rw [huv]; exact mul_ne_zero (ne_of_gt hd₁) hD
  have hwz0 : cross w z ≠ 0 := by rw [hwz]; exact mul_ne_zero (ne_of_gt hd₂) hD
  have hsin₁ := sin_angle_mul_norms_eq_abs_cross u v
  have hsin₂ := sin_angle_mul_norms_eq_abs_cross w z
  have hcos₁ := cos_angle_mul_norms_eq_inner huv0
  have hcos₂ := cos_angle_mul_norms_eq_inner hwz0
  rw [hang] at hsin₁ hcos₁
  have habsD : 0 < |D| := abs_pos.mpr hD
  rw [huv, abs_mul, abs_of_pos hd₁] at hsin₁
  rw [hwz, abs_mul, abs_of_pos hd₂] at hsin₂
  have hsin0 : Real.sin (InnerProductGeometry.angle w z) ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hsin₁
    nlinarith
  have hnorms : d₁ * (‖w‖ * ‖z‖) = d₂ * (‖u‖ * ‖v‖) := by
    have hprod : Real.sin (InnerProductGeometry.angle w z) *
        (d₂ * (‖u‖ * ‖v‖) - d₁ * (‖w‖ * ‖z‖)) = 0 := by
      linear_combination d₂ * hsin₁ - d₁ * hsin₂
    have hz := (mul_eq_zero.mp hprod).resolve_left hsin0
    linarith
  calc
    d₁ * inner ℝ w z = Real.cos (InnerProductGeometry.angle w z) *
        (d₁ * (‖w‖ * ‖z‖)) := by rw [← hcos₂]; ring
    _ = Real.cos (InnerProductGeometry.angle w z) *
        (d₂ * (‖u‖ * ‖v‖)) := by rw [hnorms]
    _ = d₂ * inner ℝ u v := by rw [← hcos₁]; ring

lemma inner_linear_combination (b c : Plane) (r s t u : ℝ) :
    inner ℝ (r • b + s • c) (t • b + u • c) =
      r * t * inner ℝ b b + s * u * inner ℝ c c +
        (r * u + s * t) * inner ℝ b c := by
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [real_inner_comm c b]
  ring

def InsideTriangle (X Y Z P : Plane) : Prop :=
  ∃ α β γ : ℝ, 0 < α ∧ 0 < β ∧ 0 < γ ∧ α + β + γ = 1 ∧
    P = α • X + β • Y + γ • Z

def InsideAngle (X Y Z P : Plane) : Prop :=
  ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ P - Y = s • (X - Y) + t • (Z - Y)

def IsCircumcentre (A K L O : Plane) : Prop :=
  dist O A = dist O K ∧ dist O A = dist O L

lemma coords_of_inside_B_midpoint_C {A B C K : Plane}
    (hK : InsideTriangle B (midpoint ℝ A B) C K) :
    ∃ x y : ℝ, 0 < x ∧ 0 < y ∧ x + y < 1 ∧
      K - A = x • (B - A) + y • (C - A) := by
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, hKeq⟩ := hK
  refine ⟨α + β / 2, γ, by positivity, hγ, ?_, ?_⟩
  · linarith
  · have hγeq : γ = 1 - α - β := by linarith
    rw [hKeq, hγeq, midpoint_eq_smul_add, invOf_eq_inv]
    module

lemma coords_of_inside_B_midpoint_C_right {A B C L : Plane}
    (hL : InsideTriangle B (midpoint ℝ A C) C L) :
    ∃ p q : ℝ, 0 < p ∧ 0 < q ∧ p + q < 1 ∧
      L - A = p • (B - A) + q • (C - A) := by
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, hLeq⟩ := hL
  refine ⟨α, γ + β / 2, hα, by positivity, ?_, ?_⟩
  · linarith
  · have hγeq : γ = 1 - α - β := by linarith
    rw [hLeq, hγeq, midpoint_eq_smul_add, invOf_eq_inv]
    module


lemma cone_determinants_pos {A B C K L : Plane} {x y p q : ℝ}
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    (hx : 0 < x) (hq : 0 < q)
    (hk : K - A = x • (B - A) + y • (C - A))
    (hl : L - A = p • (B - A) + q • (C - A))
    (hKangle : InsideAngle L B A K)
    (hLangle : InsideAngle A C K L) :
    0 < q * (1 - x) - y * (1 - p) ∧
      0 < x * (1 - q) - p * (1 - y) := by
  let b : Plane := B - A
  let c : Plane := C - A
  have hD : cross b c ≠ 0 := by
    simpa [b, c] using cross_sub_ne_zero_of_not_collinear hABC
  have hKB : K - B = (x - 1) • b + y • c := by
    calc
      K - B = (K - A) - (B - A) := by abel
      _ = (x - 1) • b + y • c := by rw [hk]; dsimp [b, c]; module
  have hLB : L - B = (p - 1) • b + q • c := by
    calc
      L - B = (L - A) - (B - A) := by abel
      _ = (p - 1) • b + q • c := by rw [hl]; dsimp [b, c]; module
  have hAB : A - B = (-1 : ℝ) • b + 0 • c := by dsimp [b, c]; module
  have hLC : L - C = p • b + (q - 1) • c := by
    calc
      L - C = (L - A) - (C - A) := by abel
      _ = p • b + (q - 1) • c := by rw [hl]; dsimp [b, c]; module
  have hAC : A - C = 0 • b + (-1 : ℝ) • c := by dsimp [b, c]; module
  have hKC : K - C = x • b + (y - 1) • c := by
    calc
      K - C = (K - A) - (C - A) := by abel
      _ = x • b + (y - 1) • c := by rw [hk]; dsimp [b, c]; module
  obtain ⟨s, t, hs, ht, hconeK⟩ := hKangle
  have hconeK' :
      (x - 1) • b + y • c =
        (s * (p - 1) - t) • b + (s * q) • c := by
    calc
      (x - 1) • b + y • c = K - B := hKB.symm
      _ = s • (L - B) + t • (A - B) := hconeK
      _ = (s * (p - 1) - t) • b + (s * q) • c := by
        rw [hLB, hAB]
        module
  obtain ⟨hxcoef, hycoef⟩ := coefficients_eq_of_cross_ne hD hconeK'
  have hd₂ : q * (1 - x) - y * (1 - p) = t * q := by
    linear_combination -q * hxcoef - (1 - p) * hycoef
  obtain ⟨u, v, hu, hv, hconeL⟩ := hLangle
  have hconeL' :
      p • b + (q - 1) • c =
        (v * x) • b + (-u + v * (y - 1)) • c := by
    calc
      p • b + (q - 1) • c = L - C := hLC.symm
      _ = u • (A - C) + v • (K - C) := hconeL
      _ = (v * x) • b + (-u + v * (y - 1)) • c := by
        rw [hAC, hKC]
        module
  obtain ⟨hpcoef, hqcoef⟩ := coefficients_eq_of_cross_ne hD hconeL'
  have hd₃ : x * (1 - q) - p * (1 - y) = u * x := by
    linear_combination -x * hqcoef - (1 - y) * hpcoef
  constructor
  · rw [hd₂]
    positivity
  · rw [hd₃]
    positivity

lemma angle_scalar_equations {A B C K L : Plane} {x y p q : ℝ}
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    (hy : 0 < y) (hp : 0 < p)
    (hk : K - A = x • (B - A) + y • (C - A))
    (hl : L - A = p • (B - A) + q • (C - A))
    (hd₂ : 0 < q * (1 - x) - y * (1 - p))
    (hd₃ : 0 < x * (1 - q) - p * (1 - y))
    (h₁ : ∠ K B A = ∠ A C L)
    (h₂ : ∠ L B K = ∠ L (midpoint ℝ A C) C)
    (h₃ : ∠ L C K = ∠ B (midpoint ℝ A B) K) :
    let b : Plane := B - A
    let c : Plane := C - A
    let U := inner ℝ b b
    let V := inner ℝ c c
    let W := inner ℝ b c
    p * (1 - x) * U = y * (1 - q) * V ∧
      (2 * p * q * (1 - x) * W - p * (1 - p) * (1 - x) * U +
        ((q * (1 - x) - y * (1 - p)) * (q - 1 / 2) - p * q * y) * V = 0) ∧
      ((x * (1 - q) - p * (1 - y)) * (x - 1 / 2) - p * x * y) * U +
        2 * x * y * (1 - q) * W - y * (1 - q) * (1 - y) * V = 0 := by
  dsimp only
  let b : Plane := B - A
  let c : Plane := C - A
  have hD : cross b c ≠ 0 := by
    simpa [b, c] using cross_sub_ne_zero_of_not_collinear hABC
  have hKB : K - B = (x - 1) • b + y • c := by
    calc
      K - B = (K - A) - (B - A) := by abel
      _ = (x - 1) • b + y • c := by rw [hk]; dsimp [b, c]; module
  have hLB : L - B = (p - 1) • b + q • c := by
    calc
      L - B = (L - A) - (B - A) := by abel
      _ = (p - 1) • b + q • c := by rw [hl]; dsimp [b, c]; module
  have hAB : A - B = (-1 : ℝ) • b + (0 : ℝ) • c := by dsimp [b, c]; module
  have hAC : A - C = (0 : ℝ) • b + (-1 : ℝ) • c := by dsimp [b, c]; module
  have hLC : L - C = p • b + (q - 1) • c := by
    calc
      L - C = (L - A) - (C - A) := by abel
      _ = p • b + (q - 1) • c := by rw [hl]; dsimp [b, c]; module
  have hKC : K - C = x • b + (y - 1) • c := by
    calc
      K - C = (K - A) - (C - A) := by abel
      _ = x • b + (y - 1) • c := by rw [hk]; dsimp [b, c]; module
  have hLN : L - midpoint ℝ A C = p • b + (q - 1 / 2) • c := by
    rw [midpoint_eq_smul_add, invOf_eq_inv]
    rw [show L = A + (p • b + q • c) by rw [← hl]; abel]
    dsimp [b, c]
    module
  have hCN : C - midpoint ℝ A C = (0 : ℝ) • b + (1 / 2 : ℝ) • c := by
    rw [midpoint_eq_smul_add, invOf_eq_inv]
    dsimp [b, c]
    module
  have hBM : B - midpoint ℝ A B = (1 / 2 : ℝ) • b + (0 : ℝ) • c := by
    rw [midpoint_eq_smul_add, invOf_eq_inv]
    dsimp [b, c]
    module
  have hKM : K - midpoint ℝ A B = (x - 1 / 2) • b + y • c := by
    rw [midpoint_eq_smul_add, invOf_eq_inv]
    rw [show K = A + (x • b + y • c) by rw [← hk]; abel]
    dsimp [b, c]
    module
  have hc₁ : cross (K - B) (A - B) = y * cross b c := by
    rw [hKB, hAB]
    calc
      cross ((x - 1) • b + y • c) ((-1 : ℝ) • b + 0 • c) =
          ((x - 1) * 0 - y * (-1)) * cross b c :=
        cross_linear_combination b c (x - 1) y (-1) 0
      _ = y * cross b c := by ring
  have hc₁' : cross (A - C) (L - C) = p * cross b c := by
    rw [hAC, hLC]
    calc
      cross (0 • b + (-1 : ℝ) • c) (p • b + (q - 1) • c) =
          (0 * (q - 1) - (-1) * p) * cross b c :=
        cross_linear_combination b c 0 (-1) p (q - 1)
      _ = p * cross b c := by ring
  have heq₁ := coeff_inner_relation_of_angle_eq
    (K - B) (A - B) (A - C) (L - C) y p (cross b c)
    hy hp hD hc₁ hc₁' h₁
  rw [hAC, hLC, hKB, hAB,
    inner_linear_combination b c 0 (-1) p (q - 1),
    inner_linear_combination b c (x - 1) y (-1) 0] at heq₁
  have hc₂ : cross (L - B) (K - B) =
      (q * (1 - x) - y * (1 - p)) * cross b c := by
    rw [hLB, hKB]
    calc
      cross ((p - 1) • b + q • c) ((x - 1) • b + y • c) =
          ((p - 1) * y - q * (x - 1)) * cross b c :=
        cross_linear_combination b c (p - 1) q (x - 1) y
      _ = (q * (1 - x) - y * (1 - p)) * cross b c := by ring
  have hc₂' : cross (L - midpoint ℝ A C) (C - midpoint ℝ A C) =
      (p / 2) * cross b c := by
    rw [hLN, hCN]
    calc
      cross (p • b + (q - 1 / 2) • c) (0 • b + (1 / 2 : ℝ) • c) =
          (p * (1 / 2) - (q - 1 / 2) * 0) * cross b c :=
        cross_linear_combination b c p (q - 1 / 2) 0 (1 / 2)
      _ = (p / 2) * cross b c := by ring
  have heq₂ := coeff_inner_relation_of_angle_eq
    (L - B) (K - B) (L - midpoint ℝ A C) (C - midpoint ℝ A C)
    (q * (1 - x) - y * (1 - p)) (p / 2) (cross b c)
    hd₂ (by positivity) hD hc₂ hc₂' h₂
  rw [hLN, hCN, hLB, hKB,
    inner_linear_combination b c p (q - 1 / 2) 0 (1 / 2),
    inner_linear_combination b c (p - 1) q (x - 1) y] at heq₂
  have hc₃ : cross (L - C) (K - C) =
      (x * (1 - q) - p * (1 - y)) * cross b c := by
    rw [hLC, hKC]
    calc
      cross (p • b + (q - 1) • c) (x • b + (y - 1) • c) =
          (p * (y - 1) - (q - 1) * x) * cross b c :=
        cross_linear_combination b c p (q - 1) x (y - 1)
      _ = (x * (1 - q) - p * (1 - y)) * cross b c := by ring
  have hc₃' : cross (B - midpoint ℝ A B) (K - midpoint ℝ A B) =
      (y / 2) * cross b c := by
    rw [hBM, hKM]
    calc
      cross ((1 / 2 : ℝ) • b + 0 • c) ((x - 1 / 2) • b + y • c) =
          ((1 / 2) * y - 0 * (x - 1 / 2)) * cross b c :=
        cross_linear_combination b c (1 / 2) 0 (x - 1 / 2) y
      _ = (y / 2) * cross b c := by ring
  have heq₃ := coeff_inner_relation_of_angle_eq
    (L - C) (K - C) (B - midpoint ℝ A B) (K - midpoint ℝ A B)
    (x * (1 - q) - p * (1 - y)) (y / 2) (cross b c)
    hd₃ (by positivity) hD hc₃ hc₃' h₃
  rw [hBM, hKM, hLC, hKC,
    inner_linear_combination b c (1 / 2) 0 (x - 1 / 2) y,
    inner_linear_combination b c p (q - 1) x (y - 1)] at heq₃
  dsimp [b, c] at heq₁ heq₂ heq₃
  refine ⟨?_, ?_, ?_⟩
  · linear_combination -heq₁
  · linear_combination 2 * heq₂
  · linear_combination 2 * heq₃

lemma p2_scalar_algebra
    (x y p q U V W : ℝ)
    (_hx : 0 < x) (hy : 0 < y) (hp : 0 < p) (hq : 0 < q)
    (hxy : x + y < 1) (hpq : p + q < 1)
    (hU : 0 < U)
    (h1 : p * (1 - x) * U = y * (1 - q) * V)
    (h2 : 2 * p * q * (1 - x) * W - p * (1 - p) * (1 - x) * U +
      ((q * (1 - x) - y * (1 - p)) * (q - 1 / 2) - p * q * y) * V = 0)
    (h3 : ((x * (1 - q) - p * (1 - y)) * (x - 1 / 2) - p * x * y) * U +
      2 * x * y * (1 - q) * W - y * (1 - q) * (1 - y) * V = 0) :
    2 * ((p + q) * (x ^ 2 * U + y ^ 2 * V + 2 * x * y * W) -
      (x + y) * (p ^ 2 * U + q ^ 2 * V + 2 * p * q * W)) -
      (x * q - y * p) * (U - V) = 0 := by
  have hax : 0 < 1 - x := by linarith
  have hbq : 0 < 1 - q := by linarith
  have hdenV : y * (1 - q) ≠ 0 := mul_ne_zero (ne_of_gt hy) (ne_of_gt hbq)
  have hdenW : 2 * p * q * (1 - x) ≠ 0 := by positivity
  have hV : V = p * (1 - x) * U / (y * (1 - q)) := by
    apply (eq_div_iff hdenV).2
    nlinarith [h1]
  have hW : W =
      (p * (1 - p) * (1 - x) * U -
        ((q * (1 - x) - y * (1 - p)) * (q - 1 / 2) - p * q * y) * V) /
        (2 * p * q * (1 - x)) := by
    apply (eq_div_iff hdenW).2
    nlinarith [h2]
  have hT :
      x * (q * (1 - x) - y * (1 - p)) =
        q * (x * (1 - q) - p * (1 - y)) := by
    have h3' := h3
    have hW' := hW
    rw [hV] at hW'
    rw [hV, hW'] at h3'
    field_simp at h3'
    have hfac : -(U *
          (x * (q * (1 - x) - y * (1 - p)) -
            q * (x * (1 - q) - p * (1 - y)))) = 0 := by
      convert h3' using 1 <;> ring
    have hn : U ≠ 0 := ne_of_gt hU
    have hfac' : U *
          (x * (q * (1 - x) - y * (1 - p)) -
            q * (x * (1 - q) - p * (1 - y))) = 0 := neg_eq_zero.mp hfac
    exact sub_eq_zero.mp (mul_eq_zero.mp hfac' |>.resolve_left hn)
  have hW' := hW
  rw [hV] at hW'
  calc
    2 * ((p + q) * (x ^ 2 * U + y ^ 2 * V + 2 * x * y * W) -
        (x + y) * (p ^ 2 * U + q ^ 2 * V + 2 * p * q * W)) -
        (x * q - y * p) * (U - V) =
        -(U * ((p + q) / (q * (1 - q)))) *
          (x * (q * (1 - x) - y * (1 - p)) -
            q * (x * (1 - q) - p * (1 - y))) := by
      rw [hV, hW']
      field_simp
      ring
    _ = 0 := by rw [sub_eq_zero.mpr hT]; ring

lemma p2_scalar_key_identity
    (x y p q U V W : ℝ)
    (hy : 0 < y) (hp : 0 < p) (hq : 0 < q)
    (hxy : x + y < 1) (hpq : p + q < 1)
    (hU : 0 < U)
    (h1 : p * (1 - x) * U = y * (1 - q) * V)
    (h2 : 2 * p * q * (1 - x) * W - p * (1 - p) * (1 - x) * U +
      ((q * (1 - x) - y * (1 - p)) * (q - 1 / 2) - p * q * y) * V = 0)
    (h3 : ((x * (1 - q) - p * (1 - y)) * (x - 1 / 2) - p * x * y) * U +
      2 * x * y * (1 - q) * W - y * (1 - q) * (1 - y) * V = 0) :
    x * (q * (1 - x) - y * (1 - p)) =
      q * (x * (1 - q) - p * (1 - y)) := by
  have hax : 0 < 1 - x := by linarith
  have hbq : 0 < 1 - q := by linarith
  have hdenV : y * (1 - q) ≠ 0 := mul_ne_zero (ne_of_gt hy) (ne_of_gt hbq)
  have hdenW : 2 * p * q * (1 - x) ≠ 0 := by positivity
  have hV : V = p * (1 - x) * U / (y * (1 - q)) := by
    apply (eq_div_iff hdenV).2
    nlinarith [h1]
  have hW : W =
      (p * (1 - p) * (1 - x) * U -
        ((q * (1 - x) - y * (1 - p)) * (q - 1 / 2) - p * q * y) * V) /
        (2 * p * q * (1 - x)) := by
    apply (eq_div_iff hdenW).2
    nlinarith [h2]
  have h3' := h3
  have hW' := hW
  rw [hV] at hW'
  rw [hV, hW'] at h3'
  field_simp at h3'
  have hfac : -(U *
        (x * (q * (1 - x) - y * (1 - p)) -
          q * (x * (1 - q) - p * (1 - y)))) = 0 := by
    convert h3' using 1 <;> ring
  have hn : U ≠ 0 := ne_of_gt hU
  have hfac' : U *
        (x * (q * (1 - x) - y * (1 - p)) -
          q * (x * (1 - q) - p * (1 - y))) = 0 := neg_eq_zero.mp hfac
  exact sub_eq_zero.mp (mul_eq_zero.mp hfac' |>.resolve_left hn)

lemma coefficient_determinant_ne_zero
    {x y p q : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hq : 0 < q)
    (hd₂ : 0 < q * (1 - x) - y * (1 - p))
    (hkey : x * (q * (1 - x) - y * (1 - p)) =
      q * (x * (1 - q) - p * (1 - y))) :
    x * q - y * p ≠ 0 := by
  intro hdet
  have hE : x * (q * (1 - x) - y * (1 - p)) -
      q * (x * (1 - q) - p * (1 - y)) = 0 := sub_eq_zero.mpr hkey
  have hsq : x * (q ^ 2 - y ^ 2) = 0 := by
    linear_combination y * hE + (x * y + q - q * y) * hdet
  have hqysq : q ^ 2 = y ^ 2 := by
    exact sub_eq_zero.mp ((mul_eq_zero.mp hsq).resolve_left (ne_of_gt hx))
  have hqy : q = y := by nlinarith
  have hxp : x = p := by
    rw [hqy] at hdet
    have : y * (x - p) = 0 := by linear_combination hdet
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left (ne_of_gt hy))
  rw [hxp, hqy] at hd₂
  linarith

lemma twice_inner_eq_inner_self_of_norm_eq_norm_sub
    {u v : Plane} (h : ‖u‖ = ‖u - v‖) :
    2 * inner ℝ u v = inner ℝ v v := by
  have hs := congrArg (fun r : ℝ => r ^ 2) h
  rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq v] at hs
  nlinarith

lemma midpoint_dist_eq_of_scalar_identity
    {A B C K L O : Plane} {x y p q : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hq : 0 < q)
    (hd₂ : 0 < q * (1 - x) - y * (1 - p))
    (hkey : x * (q * (1 - x) - y * (1 - p)) =
      q * (x * (1 - q) - p * (1 - y)))
    (hk : K - A = x • (B - A) + y • (C - A))
    (hl : L - A = p • (B - A) + q • (C - A))
    (hO : IsCircumcentre A K L O)
    (hscalar :
      2 * ((p + q) *
          (x ^ 2 * inner ℝ (B - A) (B - A) +
            y ^ 2 * inner ℝ (C - A) (C - A) +
            2 * x * y * inner ℝ (B - A) (C - A)) -
        (x + y) *
          (p ^ 2 * inner ℝ (B - A) (B - A) +
            q ^ 2 * inner ℝ (C - A) (C - A) +
            2 * p * q * inner ℝ (B - A) (C - A))) -
        (x * q - y * p) *
          (inner ℝ (B - A) (B - A) - inner ℝ (C - A) (C - A)) = 0) :
    dist O (midpoint ℝ A B) = dist O (midpoint ℝ A C) := by
  let b : Plane := B - A
  let c : Plane := C - A
  let o : Plane := O - A
  have hdet : x * q - y * p ≠ 0 :=
    coefficient_determinant_ne_zero hx hy hq hd₂ hkey
  obtain ⟨hdK, hdL⟩ := hO
  rw [dist_eq_norm, dist_eq_norm] at hdK hdL
  have hnormK : ‖o‖ = ‖o - (K - A)‖ := by
    calc
      ‖o‖ = ‖O - A‖ := by rfl
      _ = ‖O - K‖ := hdK
      _ = ‖o - (K - A)‖ := by
        congr 1
        dsimp [o]
        abel
  have hnormL : ‖o‖ = ‖o - (L - A)‖ := by
    calc
      ‖o‖ = ‖O - A‖ := by rfl
      _ = ‖O - L‖ := hdL
      _ = ‖o - (L - A)‖ := by
        congr 1
        dsimp [o]
        abel
  have hcircK := twice_inner_eq_inner_self_of_norm_eq_norm_sub hnormK
  have hcircL := twice_inner_eq_inner_self_of_norm_eq_norm_sub hnormL
  rw [hk] at hcircK
  rw [hl] at hcircL
  change 2 * inner ℝ o (x • b + y • c) =
      inner ℝ (x • b + y • c) (x • b + y • c) at hcircK
  change 2 * inner ℝ o (p • b + q • c) =
      inner ℝ (p • b + q • c) (p • b + q • c) at hcircL
  rw [inner_linear_combination b c x y x y] at hcircK
  rw [inner_linear_combination b c p q p q] at hcircL
  simp only [inner_add_right, real_inner_smul_right] at hcircK hcircL
  have hscalar' :
      2 * ((p + q) *
          (x ^ 2 * inner ℝ b b + y ^ 2 * inner ℝ c c +
            2 * x * y * inner ℝ b c) -
        (x + y) *
          (p ^ 2 * inner ℝ b b + q ^ 2 * inner ℝ c c +
            2 * p * q * inner ℝ b c)) -
        (x * q - y * p) * (inner ℝ b b - inner ℝ c c) = 0 := by
    simpa [b, c] using hscalar
  have hprod : (x * q - y * p) *
      (4 * (inner ℝ o b - inner ℝ o c) -
        (inner ℝ b b - inner ℝ c c)) = 0 := by
    linear_combination hscalar' + 2 * (p + q) * hcircK - 2 * (x + y) * hcircL
  have hmidinner :
      4 * (inner ℝ o b - inner ℝ o c) =
        inner ℝ b b - inner ℝ c c :=
    sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hdet)
  have hOM : O - midpoint ℝ A B = o - (1 / 2 : ℝ) • b := by
    rw [midpoint_eq_smul_add, invOf_eq_inv]
    dsimp [o, b]
    module
  have hON : O - midpoint ℝ A C = o - (1 / 2 : ℝ) • c := by
    rw [midpoint_eq_smul_add, invOf_eq_inv]
    dsimp [o, c]
    module
  have hsquares :
      ‖O - midpoint ℝ A B‖ ^ 2 = ‖O - midpoint ℝ A C‖ ^ 2 := by
    rw [hOM, hON,
      norm_sub_sq_real o ((1 / 2 : ℝ) • b),
      norm_sub_sq_real o ((1 / 2 : ℝ) • c),
      ← real_inner_self_eq_norm_sq ((1 / 2 : ℝ) • b),
      ← real_inner_self_eq_norm_sq ((1 / 2 : ℝ) • c)]
    simp only [real_inner_smul_left, real_inner_smul_right]
    linear_combination -(1 / 4) * hmidinner
  rw [dist_eq_norm, dist_eq_norm]
  nlinarith [norm_nonneg (O - midpoint ℝ A B), norm_nonneg (O - midpoint ℝ A C)]

theorem main_theorem
    (A B C K L O : Plane)
    (hABC : ¬ Collinear ℝ ({A, B, C} : Set Plane))
    (M N : Plane)
    (hM : M = midpoint ℝ A B)
    (hN : N = midpoint ℝ A C)
    (hK : InsideTriangle B M C K)
    (hL : InsideTriangle B N C L)
    (hKangle : InsideAngle L B A K)
    (hLangle : InsideAngle A C K L)
    (h1 : ∠ K B A = ∠ A C L)
    (h2 : ∠ L B K = ∠ L N C)
    (h3 : ∠ L C K = ∠ B M K)
    (hO : IsCircumcentre A K L O) :
    dist O M = dist O N := by
  subst M
  subst N
  obtain ⟨x, y, hx, hy, hxy, hk⟩ := coords_of_inside_B_midpoint_C hK
  obtain ⟨p, q, hp, hq, hpq, hl⟩ := coords_of_inside_B_midpoint_C_right hL
  obtain ⟨hd₂, hd₃⟩ := cone_determinants_pos hABC hx hq hk hl hKangle hLangle
  obtain ⟨heq₁, heq₂, heq₃⟩ :=
    angle_scalar_equations hABC hy hp hk hl hd₂ hd₃ h1 h2 h3
  have hD : cross (B - A) (C - A) ≠ 0 :=
    cross_sub_ne_zero_of_not_collinear hABC
  have hbne : B - A ≠ 0 := by
    intro hb
    rw [hb] at hD
    simp [cross] at hD
  have hU : 0 < inner ℝ (B - A) (B - A) :=
    real_inner_self_pos.mpr hbne
  have hscalar := p2_scalar_algebra x y p q
    (inner ℝ (B - A) (B - A))
    (inner ℝ (C - A) (C - A))
    (inner ℝ (B - A) (C - A))
    hx hy hp hq hxy hpq hU heq₁ heq₂ heq₃
  have hkey := p2_scalar_key_identity x y p q
    (inner ℝ (B - A) (B - A))
    (inner ℝ (C - A) (C - A))
    (inner ℝ (B - A) (C - A))
    hy hp hq hxy hpq hU heq₁ heq₂ heq₃
  exact midpoint_dist_eq_of_scalar_identity hx hy hq hd₂ hkey hk hl hO hscalar

