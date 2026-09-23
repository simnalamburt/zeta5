# PLAN — `irrational_zeta_five`의 `sorry`를 없애기 위한 로드맵

기준 문서: `ZETA5_IS_IRRATIONAL.pdf` (A. Fauzan, 2026-09-17). 절/식 번호는 이 논문을 따른다.
현재 상태(2026-09-23): §1.1 환원과 Phase 0, 1 완료. 남은 `sorry`는 `Zeta5/Theorem21.lean`의
네 명제(Theorem 2.1의 네 부분)이다.

## 0. 원칙

1. **논문이 옳다는 보장이 없다.** 이 논문은 미해결 난제에 대한 미심사 단독 프리프린트다. 따라서
   Lean 작업보다 먼저 수치 검증(Phase 0)으로 가장 취약한 명제를 확인하고, 거기서 깨지면 중단한다.
2. **항상 빌드가 통과하는 상태를 유지한다.** 각 Phase는 정의 + `sorry`가 붙은 명제로 시작해서
   `sorry`를 하나씩 지운다. `sorry` 개수는 이 문서 §9의 인벤토리로 추적한다.
3. **공리 검사.** CI에서 `#print axioms irrational_zeta_five`를 찍어 `sorryAx`, `Lean.ofReduceBool`
   (`native_decide`)이 없어야 완료로 본다. 유리수 구간 계산은 `norm_num`/`decide`로 하고,
   `native_decide`는 합의 없이 쓰지 않는다.
4. **논문 순서가 아니라 의존성 순서로 진행한다.** 정의(Phase 1) → 차수·양성(Phase 2, 3) →
   실수 감쇠(Phase 4) → p-진 정수성(Phase 5) → 소수 합(Phase 6) → 결합(Phase 7).
   Phase 4와 5는 독립이므로 병렬 가능하다.
5. **Mathlib 우선.** 현재 핀은 Mathlib v4.34.0. 소수정리(§6)를 외부에서 가져와야 할 때만 핀을
   올린다. TauCeti는 관련 모듈이 없어 현재로선 추가하지 않는다(§8 참조).

## 1. 최상위 분해

`exists_smallIntPolys_zeta5`는 다음 네 명제의 귀결로 재작성한다 (모두 `K = 40n`, `M = 200`).

| 이름 | 내용 | 논문 | Phase |
|---|---|---|---|
| `QKM_mem_int` | `Q_{K,M} ∈ ℤ[X]` (모든 계수의 분모가 1) | Prop 5.1 | 5 |
| `QKM_natDegree` | `deg Q_{K,M} = h = 37n` | (2.9) | 2 |
| `QKM_pos` | `Q_{K,M}(ζ(5)) > 0` | Prop 2.2 | 3 |
| `QKM_decay` | 충분히 큰 `n`에 대해 `Q_{40n,200}(ζ(5)) < exp(-139n²/5)` | (7.1), (7.2) | 4, 6, 7 |

`QKM_decay`는 다시 `log F_K(ζ(5)) ≤ U K² + 24 K log K + 200 K` (Prop 6.3, Phase 4)와
`log m_{K,M} ≤ (A_M + ε) K²` eventually (5.21, Phase 6)로 나뉜다.

## 2. Phase 0 — 수치 검증 (완료, 2026-09-23)

목적: 논문의 가장 압축된 논증(4장)이 실제로 성립하는지 컴퓨터로 확인한다. 실패하면 논문의 결함이고,
프로젝트를 중단한다.

스크립트는 `scripts/`에 있다(실행법은 `scripts/README.md`). **중단 기준에 해당하는 위반은 없었다.**

- [x] `scripts/check_local.py`: `K = 40n` (n = 1..7, 즉 K ≤ 280)에 대해 `Δ_K(X)`를 정확히 계산했다.
  - 최고차 계수는 (2.9)와, (3.11)의 행렬식의 최고차 계수는 `S_K`·(2.9)와 정확히 일치한다.
  - Lemma 3.3의 (3.10)은 모든 성분에서(n ≤ 2), (3.12)는 모든 소수에서 성립한다.
  - 외부 범위 `K/3 < p ≤ K`에서는 (4.9)가 실제로 성립하므로 Prop 4.3을 그대로 검사할 수 있다.
    모든 `p`에서 성립하고, 대부분의 `p`에서 등호 `v_p^G(Δ_K) = γ_p^out`이다. `p > K`에서 `Δ_K`는
    `p`-정수이다.
  - 내부 범위(Prop 4.1): 이 크기에서 `K ≥ 200M²`(M ≥ 40)은 불가능하고 `L_0 = 4M + 10 > h`이다.
    그래서 (4.4)~(4.8)의 배분을, 증명의 zero-source 비교가 성립하는 가장 작은 `L_0`로 돌렸다.
    이것은 논문의 `γ_p^in`보다 강한 하한이다. `p² > 5K`와 Lemma 3.1의 차수 조건(≤ p + 1)이 성립하는
    모든 `(K, p)`에서 행렬식 부등식이 성립했고 여러 경우 등호였다. 같은 경우들에서 증명의 메커니즘도
    성분별로 확인했다: 기저 (4.5)의 `ℤ_p`-유니모듈성, 각 성분의 평가 ≥ `w_{a,i} + w_{b,j}`, 나아가
    ≥ (4.2)/(4.3)의 소스별 최솟값. 검사한 소수는 K ≤ 280에서 41개, K = 400에서 18개다(x = K/p ≤ 8.5).
    조건이 깨지는 `p ∈ {7, 11, 13}`에서는 부등식이 실제로 깨지고 성분별 검사도 이를
    잡아낸다(검사가 공허하지 않다는 확인). 즉 차수 조건은 장식이 아니라 필요한 가정이다.
  - `Δ_K(ζ(5)) > 0` (arb, 엄밀), (6.14)~(6.16) 성립.
- [x] `Q_{K,M}(ζ(5))`의 감쇠 상수: `m_{K,M}`은 `K ≥ 200M²`에서만 정의되므로 `Q`를 직접 계산할 수는
      없다. 두 인자를 따로 보았다.
  - 실수 쪽: `K⁻² log F_K(ζ(5))` = −1.2758, −1.3294, −1.3478, −1.3572, −1.3628, −1.3665, −1.3692
    (K = 40, 80, …, 280). `c + a log K/K + b/K`로 외삽하면 −1.386으로(K = 160~240과 200~280 어느 쪽으로 해도 같다) `Ū = −1.3670`보다 작다(Prop 6.3과 정합).
  - 정수 쪽: `scripts/check_prime_sum.py`로 가정이 성립하는 `(K, M)`에서 `L_p(K, M)`를 논문 공식
    그대로 계산했다. 증명에 쓰인 부수 조건(`L_a ≥ 0`, 차수 ≤ p + 1, (4.9))이 모두 성립한다.
    M = 40: `K⁻² log m_{K,M}` = 1.4884 (K = 320000), 1.4774 (K = 1280000). 극한값
    `I_out + 6λ/M + ∫_3^M R x⁻³ = 1.4676`으로 수렴 중이며 `A_40 = 1.4724`보다 작다. 수렴이 느린 것은
    작은 소수 항((3.12), `O(K^{-1/2} log K)`) 때문이다. M = 200의 최소 허용값 K = 8×10^6에서는
    `K⁻² log m_{K,200} = 1.34972` (극한 1.34552, `A_200 = 1.34959`)이고 부수 조건도 모두 성립한다.
    실수 쪽 외삽값 −1.386과 합치면 `K⁻² log Q_{K,200}(ζ(5)) ≈ −0.036`으로, 목표 −139/5/1600 ≈ −0.0174
    보다 이미 작다(외삽에 기댄 추정이다).
  - (5.7)의 `O_M(1)` 오차(M = 40, K = 320000): `γ_p^in − pΓ(K/p) ∈ [−150, 149]`,
    `v_p(S_K) − pN(K/p) ∈ [3, 37]`, 외부 범위 `−γ_p^out − K(R_0 − d)(p/K) ∈ [−7, 3]`. M = 200, K = 8×10^6에서는 각각 `[−792, 741]`, `[3, 185]`, `[−7, 3]`.
  - 참고: 원시 정수 다항식 `P_K = Δ_K / cont(Δ_K)`는 이미 `K⁻² log P_K(ζ(5))` ≈ −0.17 … −0.11이다
    (K = 240에서 `P_K(ζ(5)) = e^{−6669}`). 논문이 옳다면 `P_K(ζ(5)) ≤ Q_{K,M}(ζ(5))`이다.
- [x] 부록 A (`scripts/check_potential.py`): 표 2는 **684개** 구간(약 500개가 아니다)으로 `[0, 2]`를
      정확히 분할하고, 모든 구간에서 (A.9) `B(l,r) < −6645002/10^6`이 arb로 엄밀하게 성립한다.
      가장 빡빡한 구간 (j,d,k) = (30,6,26)의 여유는 −1329/200 대비 2.7×10^-6. 분모 2^24의 dyadic
      구간이면 충분하다(§6). 표 1, (A.2), (A.10), (6.4), `V_*`, (6.8)도 확인. 참고로 표본에서
      `sup(2U^ρ − V) ≈ −6.6499` (t ≈ 0.62)로 `M_0 = −6.645`보다 0.005 아래다.
- [x] 부록 B (`scripts/check_constants.py`): 표 3, 표 4, (5.18), `I_out`, `∫d = 9/640`, `P̄`, `|C| < 16`,
      (5.16), `A*`, `A_200`, `A_100000`, (7.2)의 두 여유를 정확히 재현했다. `R(x)`의 정의 (5.4)~(5.6)과
      닫힌 형태 (5.12), (5.13), (B.1)도 4302개 유리수 점에서 일치한다.
- [x] Prop C.1은 Theorem 1.1에 불필요하므로 검증 대상에서 제외한다.
- [x] (추가) `scripts/check_functionals.py`: Phase 1에서 옮길 정의(부호, `B_1` 규약, `d(r)`)를 확인했다.
      Prop 2.2의 적분 표현(단항식, 극, 정수가 아닌 `a`에서의 Hermite 공식, `G_40(ζ(5))`의 성분)을
      수치적분으로, (3.1) 당김, (3.2), (3.3), 다항식에 대한 (3.7), `C_p ∈ p⁵ℤ_p`를 정확 연산으로.

중단 기준: 위 첫 항목에서 어떤 `p`에 대해 `v_p^G(Δ_K) < γ_p`가 관측되면 논문의 증명은 그대로는
성립하지 않는다. 사용자에게 보고하고 진행 여부를 묻는다. → 해당 없음. 남은 한계는 Prop 4.1을 논문의
실제 가정(`p > 200M`, `K ≥ 200M²`) 아래에서는 검사할 수 없었다는 점이다.

## 3. Phase 1 — 정의 (`Zeta5/Defs.lean`) (완료, 2026-09-23)

논문 §2.1, §2.2, §4, §5의 대상을 Lean 정의로 옮겼다. 증명은 기초적인 것(단항성, 차수, 양수성)만 두었다.

- [x] 상수: `K n = 40n`, `N n = 3n`, `dim n = 37n` (논문의 `h`; 가설 이름과 겹치지 않게 바꿈),
      `alpha`, `lambda`, `bigH` (2.1). `N = αK`, `h = λK`, `H = 23/20` 보조정리 포함.
- [x] `poleDen S = ∏_{j∈S} (t + j²)`, `D m = poleDen (Icc 1 m)`, `H5 j`.
- [x] 범함수: `muMon e` (2.2), `mu : ℚ[X] →ₗ[ℚ] ℚ` (`Polynomial.lsum`), `muPole j` (2.3, `X`에 대한 1차식).
- [x] 유리함수는 (분자 `A`, 극 집합 `S`)로 표현하고 `muX A S := C (mu (A /ₘ poleDen S)) +
      ∑_{j∈S} C (residue A S j) * muPole j`, `residue A S j = A(-j²) / poleDen'(-j²)`. 계획과 달리
      분모를 `D_N⁶`로 약분하지 않고 `D_K` 그대로 쓴다(`j ≤ N`의 잔차는 0). Prop 2.2의 적분 표현과
      일치함은 Phase 3에서 증명한다.
- [x] `G n : Matrix (Fin (dim n)) (Fin (dim n)) ℚ[X]` (2.4), `Δ n := det (G n)`, `S n` (2.5),
      `F n := C (S n) * Δ n`.
- [x] `Inner.gammaIn p n M` (4.4)~(4.8): `ell`, `L0`, `b`, `T`, `E`, `rank`, `eps`, `L`, `Z`, `w`, `w0`를
      각각 정의했다. 동률은 `a`의 순서로 깬다(논문은 임의). 반정수 가중치의 두 배를 정수로 합산하고,
      논문 형태와의 관계는 `Inner.gammaIn_eq`, `zeroCap2_eq`로 증명했다.
      `Outer.gammaOut p n` (4.14)는 `p > K`이면 0이다.
- [x] `Lexp p n M` (5.1, `v_p(S_K)`는 `padicValRat`), `normFactor n M` (5.2), `Q n M := C (normFactor n M) * F n`.
- [x] `Zeta5/Theorem21.lean`에 Theorem 2.1을 네 명제(`QKM_mem_int`, `QKM_natDegree`, `QKM_pos`,
      `QKM_decay`)로 나눠 `sorry`로 두고, `Main.lean`의 `exists_smallIntPolys_zeta5`는 이 네 명제로부터
      증명했다(`n ≥ 200000`이면 `K ≥ 200·200²`).
- [x] 테스트(`Zeta5Test/Defs.lean`, `lake test`): `K = 40`의 `G`, `Δ` 전체를 `norm_num`으로 대조하는 것은
      비현실적이다(37×37 행렬, 계수가 수천 자리). 대신 Phase 0 스크립트의 값과 다음을 증명으로 대조한다.
      `μ(1), μ(t), μ(t²)`, `H5 2`, `μ_X(1/(t+1))`, `μ_X(t/(t+1))`(잔차 부호), `μ_X(t³/((t+1)(t+4)))`
      (극 두 개, 1차 몫), `ℓ`, K ≤ 120의 `γ_out` 10개, `γ_in` 7개(`decide`). 틀린 값을 넣으면 `decide`가
      실패함도 확인했다. `padicValRat`는 커널에서 계산되지 않아 `v_p(S_K)`는 테스트하지 못했다.

## 4. Phase 2 — 차수 (§2.3)

- [ ] `[X] G_K = V · diag(...) · Vᵀ` (Vandermonde `V_{ij} = (-j²)^i`). Mathlib `Matrix.det_vandermonde` 사용.
- [ ] `[X^h] Δ_K = (-1)^{h(h-1)/2} ∏ j⁴ D_N(-j²)⁵ ≠ 0` (2.9). 각 인자가 0이 아님은 `positivity`급.
- [ ] 결론 `natDegree (Q K M) = h`. 규모: 작음(수백 줄).

## 5. Phase 3 — ζ(5)에서의 양성 (§2.4, Prop 2.2)

- [ ] 가중치 `w(y) := (2π)⁴ y⁵/12 ∑ ℓ⁴ e^{-2πℓy}`의 적분가능성.
- [ ] 모멘트 공식 `∫ y^{2e} w = μ(t^e)`: `∫ y^{2e+5} e^{-2πℓy} = (2e+5)!/(2πℓ)^{2e+6}`
      (Mathlib Gamma 적분 `Real.Gamma_eq_integral` 계열) + Euler 공식
      `riemannZeta_two_mul_nat` (Mathlib에 있음) + 급수·적분 교환(`integral_tsum`).
- [ ] 극 공식 `∫ w/(y²+a²) = a⁴ ζ(5,a) − 1/(2a) − 1/4`: 논문은 Hermite 적분공식(DLMF 25.11.29)을
      쓰는데 **Mathlib에 없다.** 두 가지 경로 중 택일.
      (a) Hermite 공식을 `a > 0`, `s = 5`에 대해서만 증명. 4번 부분적분 + `f(y) = 1/(e^{2πy}-1)` 전개.
      (b) 직접: `1/(y²+a²)`를 쓰지 말고 `w(y)/(y²+a²)`를 `∑_ℓ ℓ⁴ ∫ y⁵ e^{-2πℓy}/(y²+a²)`로 두고
      Laplace 변환 표현으로 `H⁽⁵⁾_j`가 나오는지 확인. (a)가 논문과 일치하므로 (a) 권장.
      Hurwitz zeta 값은 `a = j`가 정수일 때만 필요하므로 `ζ(5,j) = ζ(5) − H⁽⁵⁾_{j-1}`만 있으면 되고,
      이는 `hasSum_hurwitzZeta_of_one_lt_re`에서 나온다.
- [ ] 선형성: Phase 1의 `μ_X(R_{ij})` 정의(몫 + 잔차)가 `∫ R_{ij}(y²) w`와 같음.
- [ ] `G_K(ζ(5))`가 Gram 행렬이므로 양정치(`Matrix.PosDef`), 따라서 `det > 0`
      (`Matrix.PosDef.det_pos`). `S_K > 0`, `m_{K,M} > 0`이므로 `Q_{K,M}(ζ(5)) > 0`.
- 규모: 중간(1~2천 줄). 실해석 적분 조작이 대부분이다.

## 6. Phase 4 — 실수 감쇠 (§6, 부록 A) → Prop 6.3

Phase 5와 독립. 가장 "수학적으로 정직한" 부분이며 논문이 틀렸다면 여기서 틀릴 가능성은 낮다.

- [ ] **Andréief 항등식** (6.10): Mathlib에 없음. `det (∫ φ_i ψ_j) = (1/h!) ∫ det[φ_i(y_j)] det[ψ_i(y_j)]`.
      Leibniz 전개 + Fubini로 직접 증명. 일반형으로 별도 파일 `Zeta5/Andreief.lean`.
- [ ] Lemma 6.2 (질량 0 측도의 로그 에너지 ≤ 0): Gaussian 커널 `e^{-s|z-w|²}`의 양정치성 +
      `log r = ½∫₀^∞ (e^{-s} − e^{-sr²})/s ds`. 측도론 작업. `Zeta5/LogEnergy.lean`.
- [ ] arcsine 측도의 퍼텐셜 (A.1)과 자기 에너지 `log((b−a)/4)`: Mathlib에 없음. 치환적분으로 증명.
- [ ] 원 위 정규화 호길이 측도의 퍼텐셜 `log max(|t−u|, ε)`.
- [ ] (6.6), (6.7)~(6.9): 정규화 및 필드 수정. 부등식 조작.
- [ ] **Lemma 6.1 (A.9)**: 표 1의 16개 구간, 표 2의 684개 부분구간마다 `B(l,r) < −1329/200`을
      (A.3), (A.4)의 유리수 상·하계로 검증. 이 부분은 사실상 검증된 수치계산이다.
      계획: `log`, `arctan`, `sqrt`의 유리수 상·하계 보조정리를 한 번 만들고(Mathlib
      `Real.log_le_sub_one_of_pos`, `Real.abs_log_sub_add_sum_range_le`, `Real.arctan` 급수 등 확인 필요),
      각 구간은 `norm_num`으로 닫는다. Phase 0 결과: 논문의 2^-144 대신 **분모 2^24의 dyadic 구간**이면
      −1329/200을 증명하기에 충분하다(분모 2^26이면 −6645002/10^6까지). 가장 빡빡한 구간은
      (j,d,k) = (30,6,26)으로 여유가 2.7×10^-6이다. 여기가 이 Phase의 시간 대부분이다.
- [ ] (A.10) `I(ρ)`, `C*`의 유리수 구간 → (6.4).
- [ ] 스케일링 (6.12), 가중치 상계 (6.11), 계승 부등식 (Mathlib `Stirling` 파일 참고), (6.14), (6.15).
- [ ] Prop 6.3.
- 규모: 큼(3~5천 줄 + 수치 검증 파일).

## 7. Phase 5 — p-진 정수성 (§3–§4) → Prop 5.1

가장 위험한 Phase. Phase 0에서 검증한 뒤에만 착수한다.

- [ ] §3 범함수 `τ`, 당김 (3.1), 반사·차분 항등식 (3.2), (3.3). Bernoulli 다항식의 `B_n(1−x)`,
      `B_n(x+1) − B_n(x)` 항등식은 Mathlib `Polynomial.bernoulli`에 일부 있음(확인 필요).
- [ ] **Bernoulli 곱셈 정리** (DLMF 24.4.18, Lemma 3.2에 필요): Mathlib에 없음. 생성함수로 증명.
- [ ] von Staudt–Clausen: Mathlib `Bernoulli.vonStaudt_clausen` 있음 → `v_p(κ_d) ≥ −1`.
- [ ] Tate 대수 `ℚ_p⟨z⟩`: Mathlib에 없음. 논문은 수렴 급수의 연속 확장을 쓰지만, 실제로 필요한 것은
      **유한 절단**에서의 평가 하한이므로 `PowerSeries ℚ_p`의 계수 하한 조건으로 대체하는 것을
      권장한다. Lemma 3.1을 이 형태로 다시 서술한다.
- [ ] (3.5) 원거리 극의 전개, Lemma 3.2 분배 공식.
- [ ] Lemma 3.3 (작은 소수): 정수값 다항식의 이항 기저(Mathlib `Polynomial.binomial`? 없으면 직접),
      (3.8), (3.9), (3.10). 기저 변환 (3.11)과 (3.12).
- [ ] **Prop 4.1 (내부 범위)**: CRT로 만든 `ℤ_p`-유니모듈러 기저 (4.5), 가중치 (4.6)~(4.8),
      "각 성분의 평가 ≥ 두 행 가중치의 합"에서 `det`의 Gauss 평가 하한. 논문의 서술이 가장
      압축된 곳이며 Phase 0의 검증 대상이다. `Polynomial.gaussNorm`(Mathlib에 있음)을 평가로 쓴다.
- [ ] Lemma 4.2: 여인자 전개(complementary minors). Mathlib에는 일반 Laplace 전개가 없어
      `Matrix.det_add`류를 직접 증명해야 한다. `Zeta5/DetRank.lean`.
- [ ] Prop 4.3 (외부 범위) 및 `p > K`.
- [ ] Legendre 공식 (5.3): Mathlib `padicValNat_factorial` 계열 사용.
- [ ] Prop 5.1: 모든 `p`에 대해 `v_p(m_{K,M} F_K) ≥ 0` → 계수가 정수.
- 규모: 매우 큼(5천~1만 줄).

## 8. Phase 6 — 소수 합 (§5.1–5.3, 부록 B) → (5.21)

- [ ] **소수정리 점근형**: Mathlib에는 Chebyshev 함수 `θ, ψ`와 유계만 있고 `θ(x) ~ x`는 없다.
      0.2% 마진 때문에 Chebyshev 상수로는 대체 불가. 선택지:
      (a) `PrimeNumberTheoremAnd` 프로젝트를 의존성으로 추가(Mathlib 핀 상향 필요).
      (b) 필요한 형태 `∑_{K/M<p≤K/3} p f(K/p) log p / K² → ∫ f(x)/x³ dx`만 부분합으로 유도하되
      `θ(x) = x + o(x)`는 외부에서 가져온다. (a)+(b) 조합이 현실적이다. 이 결정은 사용자 확인 필요.
- [ ] (5.7): `γ_p^in = p Γ(K/p) + O_M(1)`. 논문은 스케치만 있고 `O_M(1)` 균일성이 핵심이다.
      명시적 상수로 다시 써야 한다(Phase 0에서 수치로 상수 추정).
- [ ] 외부 범위 (5.8)~(5.10), `I_out = 127751/96000`: 부록 B 표 4의 조각별 적분(`norm_num`).
- [ ] 내부 적분 (5.18): 143개 구간에서 `R`이 1차식임을 보이고 적분(`norm_num`).
- [ ] 꼬리 (5.15)~(5.17): 부분적분과 주기함수 `P, C`의 유계.
- [ ] Prop 5.2, (5.21) `limsup K⁻² log m_{K,M} ≤ A_M`.
- 규모: 큼. 소수정리 의존성이 결정되기 전까지는 (5.7) 이하 부등식 부분만 진행한다.

## 9. Phase 7 — 결합 (§7)

- [ ] (7.1): Prop 6.3 + (5.21) → `limsup K⁻² log Q_{K,M}(ζ(5)) ≤ A_M + U`.
- [ ] (7.2) `−1600(A_200 + U) > 139/5`: 유리수 산술, `norm_num`. 2026-09-23에 Python으로 재현 완료.
- [ ] `limsup` 형태를 `∀ᶠ n, Q_{40n,200}(ζ(5)) < exp(−139n²/5)`로 변환.
- [ ] `exists_smallIntPolys_zeta5`의 `sorry` 제거 → `#print axioms irrational_zeta_five` 확인.

## 10. 파일 구성(안)

```
Zeta5/Main.lean        -- 최종 정리와 §1.1 환원 (완료)
Zeta5/Defs.lean        -- Phase 1 (완료)
Zeta5/Theorem21.lean   -- Theorem 2.1의 네 명제. Phase 7에서 각 Phase의 결과를 모은다
Zeta5/Degree.lean      -- Phase 2
Zeta5/Moment.lean      -- Phase 3: w, 모멘트, Hermite 공식, 양정치
Zeta5/Andreief.lean    -- Phase 4
Zeta5/LogEnergy.lean   -- Phase 4: Lemma 6.2, arcsine 퍼텐셜
Zeta5/Potential.lean   -- Phase 4: 부록 A 표 1, 표 2 검증
Zeta5/RealBound.lean   -- Phase 4: Prop 6.3
Zeta5/Bernoulli.lean   -- Phase 5: τ, 곱셈 정리, 반사·차분
Zeta5/Local.lean       -- Phase 5: Lemma 3.1~3.3
Zeta5/DetRank.lean     -- Phase 5: Lemma 4.2
Zeta5/Inner.lean       -- Phase 5: Prop 4.1
Zeta5/Outer.lean       -- Phase 5: Prop 4.3
Zeta5/Integrality.lean -- Phase 5: Prop 5.1
Zeta5/PrimeSum.lean    -- Phase 6
Zeta5/Constants.lean   -- Phase 6, 7: 부록 B 유리수 상수
Zeta5Test/            -- 정의의 작은 경우 테스트 (`lake test`)
scripts/               -- Phase 0 수치 검증
```

## 11. 외부 라이브러리

- **TauCeti** (https://github.com/TauCetiProject/TauCeti): 로그 퍼텐셜, Hankel 행렬식, 소수정리,
  Bernoulli 곱셈 정리 중 어느 것도 없음(2026-09-23 확인). Mathlib `master`를 고정하므로 추가하면
  이 프로젝트의 핀도 올려야 한다. 현재는 추가하지 않는다. Phase 6에서 핀을 올리게 되면 재검토.
- **PrimeNumberTheoremAnd**: 소수정리 점근형의 유일한 현실적 출처. Phase 6 착수 시 결정.

## 12. `sorry` 인벤토리 (진행 상황 추적)

| Lean 이름 | Phase | 상태 |
|---|---|---|
| `Zeta5.irrational_of_smallIntPolys` | — | 완료 |
| `Zeta5.exists_smallIntPolys_zeta5` | 1 | 완료 (아래 네 명제로부터) |
| `QKM_natDegree` | 2 | `sorry` (`Theorem21.lean`) |
| `QKM_pos` | 3 | `sorry` (`Theorem21.lean`) |
| `hermite_integral_five` | 3 | 미착수 |
| `andreief` | 4 | 미착수 |
| `logEnergy_nonpos_of_zero_mass` | 4 | 미착수 |
| `potential_bound_A9` | 4 | 미착수 |
| `realBound_prop63` | 4 | 미착수 |
| `bernoulli_multiplication` | 5 | 미착수 |
| `local_small_primes_33` | 5 | 미착수 |
| `inner_range_41` | 5 | 미착수 (Phase 0 검증 선행) |
| `det_rank_42` | 5 | 미착수 |
| `outer_range_43` | 5 | 미착수 |
| `QKM_mem_int` | 5 | `sorry` (`Theorem21.lean`) |
| `prime_sum_52` | 6 | 미착수 (소수정리 의존성 결정 선행) |
| `normalization_growth_521` | 6 | 미착수 |
| `QKM_decay` | 7 | `sorry` (`Theorem21.lean`) |

## 13. 리스크

1. **논문 자체의 오류** (특히 Prop 4.1, (5.7)의 균일성). Phase 0에서는 반례를 찾지 못했다(§2).
   다만 Prop 4.1은 가정 `K ≥ 200M²`이 성립하는 영역에서 직접 검사할 수 없었으므로, 형식화 중에
   증명의 빈틈이 드러날 가능성은 남아 있다.
2. **소수정리 부재.** Mathlib 핀 상향과 외부 의존성 필요. 사용자 결정 사항.
3. **수치 검증의 규모.** 표 2의 684개 구간 × 유리수 `norm_num`. Phase 0에서 필요한 정밀도가
   2^-24임을 확인했다. 그래도 느리면 검증된 구간산술 전술을 별도로 작성해야 한다.
4. **Tate 대수·연속 확장.** Mathlib에 없으므로 유한 절단으로 재서술. 논문과의 동치성을 별도로
   증명해야 한다.
5. **총 규모.** 대략 1.5만~2.5만 줄의 Lean. 한 사람이 진행하면 연 단위 작업이다.
