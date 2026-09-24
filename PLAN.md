# PLAN — `irrational_zeta_five`의 `sorry`를 없애기 위한 로드맵

기준 문서: `ZETA5_IS_IRRATIONAL.pdf` (A. Fauzan, 2026-09-17). 절/식 번호는 이 논문을 따른다.
현재 상태(2026-09-24): §1.1 환원과 Phase 0~5 완료. `QKM_decay`는 `realBound`(Phase 4, 완료)와
`normFactor_growth`(Phase 6)로부터, `QKM_mem_int`는 Prop 5.1(Phase 5, 완료)로부터 증명되었다.
남은 `sorry`는 `normFactor_growth`(Phase 6) 하나다(§12).

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
5. **Mathlib 우선.** 현재 핀은 Mathlib v4.32.2(Lean v4.32.2)로, 소수정리를 가져오는
   PrimeNumberTheoremAnd의 핀에 맞춘 것이다(2026-09-24, v4.34.0에서 내림). 이 버전에 없는 Mathlib
   보조정리는 `Zeta5/Compat.lean`(같은 이름)과 `Zeta5/Frullani.lean`에 증명해 두었고, 핀을 올릴 때
   지운다. 구버전 `convert`가 인스턴스 목표를 남기는 곳에는
   `all_goals try with_reducible_and_instances rfl`을 넣었다. 헤더 린터는 이 버전에서 라이선스 문구를
   설정할 수 없어 꺼 두었다(`lakefile.toml`). TauCeti는 관련 모듈이 없어 추가하지 않는다(§8 참조).

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

## 4. Phase 2 — 차수 (§2.3, `Zeta5/Degree.lean`) (완료, 2026-09-24)

- [x] `G_eq`: 각 성분이 `X`에 대해 1차이므로 `G = X • B + A` (`Glin`, `Gconst`). Mathlib
      `coeff_det_X_add_C_card`로 `[X^h] Δ_K = det B` (`coeff_Δ_dim`), `natDegree_det_X_add_C_le`로 차수 ≤ h.
- [x] `Glin_eq`: `j ≤ N`의 잔차는 0이고 남는 극은 `N < j ≤ K`의 정확히 `h`개이므로
      `B = Vᵀ · diag(c) · V`, `V_{kj} = (-(N+1+k)²)^j` (Mathlib `vandermonde`).
      `det B = (det V)² ∏ c_k ≠ 0` (`det_vandermonde_ne_zero_iff`; `c_k ≠ 0`은 `D_N(-j²) ≠ 0`과
      `D_K`의 분리성 `separable_prod_X_sub_C_iff'`에서).
- [x] `natDegree_Q : (Q n M).natDegree = dim n` (모든 `n`, `M`). `QKM_natDegree`의 `sorry`를 제거했다.
- 계획과 달리 (2.9)의 선행계수 값 `(-1)^{h(h-1)/2} ∏ j⁴ D_N(-j²)⁵` 자체는 증명하지 않았다.
  차수에는 `≠ 0`만 필요하다(Phase 0에서 값은 수치로 확인했다). 약 190줄.

## 5. Phase 3 — ζ(5)에서의 양성 (§2.4, Prop 2.2) (완료, 2026-09-24)

`QKM_pos`의 `sorry`를 제거했다(표준 공리만 사용). 약 1400줄, 네 파일.

- [x] `Zeta5/Weight.lean`: 가중치 `wt`(급수로 정의), 양수성, 합가능성, 적분가능성
      (모멘트 적분값이 양수라는 것에서 `Integrable.of_integral_ne_zero`로 얻는다).
      모멘트 공식 `integral_pow_mul_wt : ∫ y^{2e} w = μ(t^e)`는 Gamma 적분
      `integral_rpow_mul_exp_neg_mul_Ioi`와 Euler 공식 `hasSum_zeta_nat`으로 증명했다.
- [x] 극 공식 `integral_wt_div_sq_add_sq : ∫ w/(y²+j²) = j⁴(ζ(5) − H_j⁽⁵⁾) − 1/4 + 1/(2j)`.
      **Hermite 적분공식 없이** 증명했다(`Zeta5/Hermite.lean`, `Zeta5/PoleIntegrals.lean`).
      1. `g = y⁵/(y²+a²)`에 대해 ℓ별로 4번 부분적분하면 `∫ c⁴e^{−cy} g = 24a⁴ ∫ e^{−cy} r₅`이다.
         여기서 `r₅ = Re((y−ia)⁻⁵)`이고, 경계항은 `g,…,g‴(0) = 0`이라 사라진다.
         ℓ에 대해 합하면 `∫ w/(y²+a²) = 2a⁴ ∫ f r₅`, `f = 1/(e^{2πy}−1)`이다.
      2. Mathlib `cot_series_rep'`와 `Complex.cot_pi_eq_exp_ratio`를 `iy`에 적용해
         `f = −1/2 + 1/(2πy) + (1/π)∑_{k≥1} y/(y²+k²)`를 얻는다.
      3. 세 유리함수 적분 `∫r₅ = 1/(4a⁴)`, `∫r₅/y = π/(2a⁵)`,
         `∫ y/(y²+k²) r₅ = π/(2(a+k)⁵)`은 명시적 원시함수로 계산했다. 원시함수는 computer algebra로
         찾았고 Lean에서는 미분해서 검증한다(`a = k`는 별도 원시함수). 결과는 실수 `a > 0` 전체에 대한
         `∫ w/(y²+a²) = a⁴ζ(5,a) − 1/(2a) − 1/4`이다.
- [x] `Zeta5/Gram.lean`: 부분분수(`modByMonic_poleDen`, Lagrange 유일성)로
      `aeval ζ(5) (muX A S) = ∫ A(y²)/∏(y²+j²) · w`를 증명했다(Prop 2.2). `G_K(ζ(5))`는 가중치
      `D_N(y²)⁶/D_K(y²)·w`에 대한 `1, y², …`의 Gram 행렬이므로 `Matrix.PosDef`이고, `det_pos`로
      `Δ_K(ζ(5)) > 0`을 얻는다. 양정치성은 이차형식의 피적분함수가 유한개 근을 제외한 `(0,∞)`에서
      양수라는 것으로 보였다.

## 6. Phase 4 — 실수 감쇠 (§6, 부록 A) → Prop 6.3 (완료, 2026-09-24)

Prop 6.3은 **점근형**으로 증명한다: 모든 `ε > 0`에 대해 결국 `log F_K(ζ(5)) ≤ (Ū + ε) K²`
(`Zeta5/RealBound.lean`의 `realBound`). 논문의 명시적 `24 K log K + 200 K`는 필요 없고, 이 덕분에
§6의 모든 저차항을 `o(K²)`로 다룰 수 있다. `QKM_decay`는 `realBound`와 `normFactor_growth`(5.21)로부터
`δ = −1600(A_200 + Ū) − 139/5 > 0`(`Constants.margin_72_pos`)을 이용해 증명했다.

- [x] **Andréief 항등식** (6.10): `Zeta5/Andreief.lean`. Leibniz 전개 + `integral_fintype_prod_eq_prod`.
- [x] (6.15) `log S_K`: `Zeta5/LogS.lean`. Stirling(`Stirling.log_stirlingSeq'_antitone`)과
      `∑ log((2i)!) ≥ ∫`를 `x²log(2x) − 3x²/2`의 증분으로 비교.
- [x] (6.11), (6.12): `Zeta5/Field.lean` (`wt_le`, `sum_log_ge`, `sum_log_le`).
- [x] (6.14) `log Δ_K`: `Zeta5/LogDelta.lean`. Andréief → 점별 상계
      `vdet² ∏ρ ≤ e^B ∏ψ(y_k)`(`ψ = 2^17(1+y^17)e^{−y/K}`) → 적분.
- [x] **Lemma 6.2** (질량 0 측도의 로그 에너지 ≤ 0): `Zeta5/LogEnergy.lean`.
      논문의 원(반지름 ε) 정규화 대신 **커널 `log((x−y)² + δ²)`로 정규화**했다. 이러면 커널이 받침 위에서
      유계라 극한 논법이 필요 없다. Gaussian 커널의 양정치성(제곱 완성 + Fubini)과 Mathlib의
      Frullani 적분 `∫₀^∞ s⁻¹(e^{-as} − e^{-bs}) ds = log(b/a)`(`Zeta5/Frullani.lean`, Fubini로 직접
      증명; 처음에는 Mathlib의 `Frullani.integral_Ioi_eq`를 썼으나 v4.32.2에는 없다)으로 증명.
- [x] arcsine 측도와 퍼텐셜 (A.1): `Zeta5/Arcsine.lean`. arcsine 측도를 `θ ↦ m + R cos θ`에 의한
      균등분포의 상으로 정의하면 적분이 원평균이 된다. Joukowski 인수분해
      `|c − Re z| = |z − w||z − w'|/2` (`w + w' = 2c`, `ww' = 1`)와 Mathlib의
      `circleAverage_log_norm_sub_const_eq_posLog`로 (A.1)을 얻는다.
- [x] 교차항 오차: `Zeta5/Regularize.lean`. 논문의 `60√ε` 대신, 정규화된 퍼텐셜이 `2U`로 **균등
      수렴**한다는 것을 Dini 정리(`Antitone.tendstoUniformlyOn_of_forall_tendsto`)로 보였다.
      필요한 것은 `o(1)`뿐이므로 ρ의 질량-공 상계가 필요 없다.
- [x] ρ (표 1), `U^ρ`, `I(ρ)`: `Zeta5/Rho.lean`. `I(ρ)`는 (A.2)의 닫힌 꼴
      `∑_{j,k} c_j c_k log((b_m − a_m)/4)` (`m = max(j,k)`)로 **정의**하고, 필요한 부등식
      `∫∫ log((x−y)²+δ²) dρdρ ≥ 2I(ρ)`만 증명했다(중첩 구간에서 큰 구간의 퍼텐셜이 상수).
- [x] (6.7), (6.8), (6.9): `Zeta5/Energy.lean`의 `energy_bound`. `t ≥ 2`는 (6.8)을 직접 증명.
- [x] **`potential_le_M0`** (Lemma 6.1의 (6.2), `0 < t ≤ 2`): `Zeta5/Potential.lean`. 표 2의 684개
      구간에서 (A.9)를 검증한다. 구성:
      * `Zeta5/Enclose.lean`: `log`(artanh 급수 + `2ᵉ` 환원), `arctan`(교대급수 + `π/4`, `π/2` 환원),
        `√`(Newton 추측값을 제곱으로 검사), `π`(Mathlib 20자리)의 유리수 상·하계와 건전성 증명.
        중간값은 `2⁻⁴⁰`의 배수로 반올림한다.
      * `Zeta5/VClosed.lean`: (A.5) `V(s²) = Φ(s)`(FTC), `Φ' = 2P`, `P`가 `[0, 1/2]`에서 증가
        (`P' ≥ 0 ⟺ s² ≤ 711/880`), `[1/2, ∞)`에서 `P ≥ 0`(`arctan(s/α) ≥ π/3`). 따라서
        `P(√q₋) ≤ 0 ≤ P(√q₊)`이면 `V`는 `(0, q₋]`에서 감소, `[q₊, ∞)`에서 증가.
      * `U^{ω_j}(t)`는 `|t − m_j|`의 증가함수이므로 `[l, r]`에서 `max(U(l), U(r))`로 막힌다.
        `[q₋, q₊]`에서는 (A.5)의 단조 조각으로 `V ≥ V*`.
      * 검사기 `checkIv`/`checkChain`을 `decide +kernel`로 실행(76구간씩 9개 정리, 약 280초, 최대
        메모리 12.5GB). 분할점은 `Zeta5/PotentialData.lean`(`scripts/gen_table2.py`로 생성);
        검사기의 건전성은 분할점 목록에 의존하지 않는다.
      * Phase 0의 Python 원형과 같은 알고리즘이다: 가장 빡빡한 구간 (30,6,26)의 여유 2.69×10⁻⁶.
- [x] **`energy_const_le`** (6.4), (A.10): `Zeta5/RealBound.lean`. `I(ρ)`의 16개 로그와 `log α`,
      `log 2λ`를 `Enclose.logLo`로 막고 `decide +kernel`로 `λM₀ − I(ρ) + C* ≤ Ū`를 확인한다.
- 결과: `realBound`(Prop 6.3 점근형)는 표준 공리(`propext`, `Classical.choice`, `Quot.sound`)만 쓴다.
  `native_decide`는 쓰지 않는다(`decide +kernel`은 커널 검사라 추가 공리가 없다).

## 7. Phase 5 — p-진 정수성 (§3–§4) → Prop 5.1 (완료, 2026-09-24)

`QKM_mem_int`는 `Zeta5/Integrality.lean`의 `QKM_integral`(Prop 5.1)이고, 이는 네 개의 국소
하한(`Zeta5/LocalBounds.lean`)에서 나온다. 모두 표준 공리만 쓴다. 평가는 `VGe p w q`
(`‖q‖_p ≤ p^{−w}`)와 계수별 `PolyVGe`로 다루고, 가중치는 두 배(정수)로 쓴다(`PBound.lean`).
논문과 다른 길을 택한 곳이 여럿 있다. 특히 **Lemma 3.1, 3.2(분배 공식)와 Tate 대수는 쓰지 않는다.**

- [x] §3 범함수: `Tau.lean`. `τ(P) = L(P''')/24`, `κ_d = τ(x^d)`, 차분 항등식 (3.3),
      Bernoulli 곱셈 정리(최종 증명에는 불필요해졌다), 극이 정수인 유리함수의 `τ_X`(`tauR`),
      당김 (3.1) `μ_X(A/D_S) = τ_X(x⁵A(−x²)/D_S(−x²))`(`muX_eq_tauR`).
- [x] 값 경계 (3.9): `Binom.lean`. Newton 공식과 이항 기저의 계수 경계로
      `v_p(τ(Q)) ≥ min v_p(Q(n)) − 4⌊log_p D⌋`. 논문의 `−v_p(24)` 손실이 없다(`τ(ΔF) = [x⁴]F`).
      `ValueTau.lean`: 임의의 연속 정수 `D`개에서의 값으로 같은 경계(이동한 이항 기저).
- [x] **Lemma 3.3과 (3.11), (3.12)**: `SmallPrimes.lean`, `SmallPrimeBound.lean`. `C(x+K, k)` 기저로
      전개하고, `k ≤ 2K`는 유수(`(K!)²/∏(r−s)`의 평가를 배수 세기로), `k > 2K`는 다항식 부분의 값
      (각 `p^j` 단계에서 손실 ≤ 2)으로 막는다. 논문의 공(ball) 논법(`M₀`, (3.8))은 쓰지 않는다.
      기저 `q_i`의 정수값성은 연속 정수의 곱으로 보였다.
- [x] `p > K`: `BigPrimes.lean`. **기저 변환 없이** `G_K`의 모든 성분이 정수다. `|r| < p`인 극에서
      합동인 쌍은 `r, r − p`뿐이고, `H⁽⁵⁾_m ≡ H⁽⁵⁾_{p−1−m}`(`LocalTau.lean`)으로 나눗셈 차분이
      정수가 된다. 다항식 부분은 `κ_d`가 `d ≤ 4p − 2`에서 정수(von Staudt–Clausen)라서 정수.
- [x] **Prop 4.1 (내부 범위)**: `InnerRange.lean` 외. 분배 공식 대신 **값 경계**를 쓴다: 창
      `K+1, …, K+D`(`D = 104n+2`, `p² > 200K`)에서 `Q(n) = g(n) − ∑ Res_r/(n−r)`이고, 극 `r`의
      유수는 `v ≥ E_c + 1`, 창의 값은 `v ≥ E_c`(`c`는 `r`, `n`의 제곱류)이므로 성분 평가가
      `min_c E_c − 4` 이상이다(`InnerEntry.lean`의 `PolyVGe_entry`). 이는 (4.2), (4.3)과 같다.
      Lemma 3.1의 차수 조건(`≤ p + 1`) 대신 필요한 조건은 창의 길이 `D < p²`와 `2K + D < p²`이다.
      그 뒤는 논문대로: CRT 유니모듈러 기저 (4.5)(`Unimodular.lean`), `L_a ≥ 0`과 `∑ L_a = h`
      (`InnerCount.lean`; 순위의 전단사, `pℓ_N(a) ≤ 2N + p`), 반가중치 비교
      (`Zc − Za + 1 + (ℓ_K(a) − ℓ_K(c))/2 ≥ 0`).
- [x] **Lemma 4.2**: `DetBound.lean`. 여인자 전개 없이 두 갈래로: `−z`는 영 가중치를 `−1/2`로 낮추면
      `p⁻¹L`의 성분이 가중치 조건을 만족하는 것에서, `−r`은 `det(A + p⁻¹UL'Uᵀ)`를 블록 행렬
      `[[A, −U], [p⁻¹L'Uᵀ, 1]]`(Schur)의 행렬식으로 보고 행·열 가중치를 따로 둔 행렬식 경계로.
- [x] **Prop 4.3 (외부 범위)**: `OuterClass.lean`, `OuterEntry.lean`, `OuterRange.lean`.
      `τ = τ_low + p⁻¹τ_high`(`d ≤ 4p−2`의 모멘트만 남김)로 `G = A + p⁻¹L`, `L`은 단항식 기저에서
      마지막 `r_p`개 행·열에만 있다. 논문은 `c_e ≡ pμ(t^e) (mod p)`인 정수 `c_e`를 고르지만, 여기서는
      `e ≥ 2p − 3`에서 `c_e = pμ(t^e)` 그대로(즉 `μ₀(t^e) = 0`)를 쓴다. 기저 (4.11), 성분 경계 (4.12)(극별 경계와 나눗셈 차분),
      정확한 류 크기 `ℓ_K(c) = 2⌊K/p⌋ + [c ≤ v] + [c ≥ p−v]`로 가중치 합과 영 가중치 개수를
      (4.14)와 비교한다. 비교는 등식이 아니라 부등식(`∑ w ≥` 공식의 주항, `z ≤` 공식의 영 가중치
      수)으로 한다. 영 류(`p, 2p`)의 행은 논문의 `1, t + p²` 대신 `1, t`(`(t + 0²)^i`)이고, 가중치는
      논문의 `(−2, 0)` 대신 `(−3/2, 0)`도 성립하므로 그것을 썼다(`K ≥ 2p`에서 1만큼 더 강함;
      `γ_p^out` 이하임을 보이는 데는 문제 없다).
- [x] Prop 5.1: `Integrality.lean`. `p ≤ 2h`에서는 (5.1)의 경우별로, `p > 2h`에서는 `S_K`가 단원.
- 규모: 새 파일 22개, 약 5.7천 줄.

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
Zeta5/Theorem21.lean   -- Theorem 2.1의 네 명제
Zeta5/Degree.lean      -- Phase 2 (완료)
Zeta5/Weight.lean      -- Phase 3: w와 모멘트 (완료)
Zeta5/PoleIntegrals.lean -- Phase 3: 극 공식의 유리함수 적분 (완료)
Zeta5/Hermite.lean     -- Phase 3: 극 공식 (완료)
Zeta5/Gram.lean        -- Phase 3: 부분분수, Gram 양정치성 (완료)
Zeta5/Andreief.lean    -- Phase 4: Andréief 항등식 (완료)
Zeta5/Field.lean       -- Phase 4: V, Riemann 합 (6.12), 가중치 상계 (6.11) (완료)
Zeta5/LogS.lean        -- Phase 4: (6.15) (완료)
Zeta5/LogDelta.lean    -- Phase 4: (6.14) (완료)
Zeta5/LogEnergy.lean   -- Phase 4: Lemma 6.2 (정규화 커널) (완료)
Zeta5/Arcsine.lean     -- Phase 4: arcsine 측도와 (A.1) (완료)
Zeta5/Regularize.lean  -- Phase 4: 정규화 퍼텐셜의 균등수렴 (Dini) (완료)
Zeta5/Rho.lean         -- Phase 4: 표 1의 ρ, U^ρ, I(ρ) (완료)
Zeta5/Enclose.lean     -- Phase 4: log, arctan, √, π의 유리수 상·하계 (완료)
Zeta5/VClosed.lean     -- Phase 4: (A.5), V의 단조성 (완료)
Zeta5/Potential.lean   -- Phase 4: (6.2)의 수치 검증 (A.9) (완료)
Zeta5/PotentialData.lean -- Phase 4: 표 2의 분할점 (생성됨)
Zeta5/Energy.lean      -- Phase 4: (6.7)~(6.9) (완료)
Zeta5/RealBound.lean   -- Phase 4: Prop 6.3 점근형, (A.10) (완료)
Zeta5/PoleDen.lean     -- Phase 5: `poleDen`의 부분분수 (Gram.lean에서 분리)
Zeta5/Tau.lean         -- Phase 5: τ, τ_X, 당김 (3.1) (완료)
Zeta5/PBound.lean      -- Phase 5: VGe/PolyVGe, 가중치 행렬식 경계, 정수성 판정 (완료)
Zeta5/Binom.lean       -- Phase 5: Newton 공식, 값 경계 (3.9) (완료)
Zeta5/Count.lean       -- Phase 5: 구간의 배수 세기 (완료)
Zeta5/SmallPrimes.lean -- Phase 5: Lemma 3.3 (완료)
Zeta5/SmallPrimeBound.lean -- Phase 5: (3.11), (3.12) (완료)
Zeta5/GramBasis.lean   -- Phase 5: Gram 행렬의 기저 변환 (완료)
Zeta5/LocalTau.lean    -- Phase 5: ℤ_(p), κ_d, H⁽⁵⁾ 합동, 나눗셈 차분 (완료)
Zeta5/BigPrimes.lean   -- Phase 5: p > K (완료)
Zeta5/Unimodular.lean  -- Phase 5: CRT 기저의 유니모듈러성 (완료)
Zeta5/ValueTau.lean    -- Phase 5: 창에서의 값 경계 (완료)
Zeta5/SqClass.lean     -- Phase 5: 제곱류와 평가 (완료)
Zeta5/InnerEntry.lean  -- Phase 5: (4.2), (4.3) (완료)
Zeta5/InnerCount.lean  -- Phase 5: (4.4)~(4.7)의 배정 (완료)
Zeta5/InnerRange.lean  -- Phase 5: Prop 4.1 (완료)
Zeta5/DetBound.lean    -- Phase 5: Lemma 4.2 (완료)
Zeta5/OuterClass.lean  -- Phase 5: 외부 범위의 류 (완료)
Zeta5/OuterEntry.lean  -- Phase 5: τ_low, τ_high, 극별 경계, 나눗셈 차분 (완료)
Zeta5/OuterRange.lean  -- Phase 5: Prop 4.3 (완료)
Zeta5/LocalBounds.lean -- Phase 5: 네 국소 하한 (완료)
Zeta5/Integrality.lean -- Phase 5: Prop 5.1 (완료)
Zeta5/PrimeSum.lean    -- Phase 6: normFactor_growth (5.21)
Zeta5/Constants.lean   -- 부록 B 유리수 상수 (Ū, A_M, (7.2)의 여유) (완료)
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
| `QKM_natDegree` | 2 | 완료 (`Degree.lean`의 `natDegree_Q`) |
| `QKM_pos` | 3 | 완료 (`Gram.lean`의 `aeval_Q_pos`) |
| `integral_wt_div_sq_add_sq` (극 공식) | 3 | 완료 (Hermite 공식 없이) |
| `andreief` | 4 | 완료 |
| `logEnergy_nonpos` (Lemma 6.2) | 4 | 완료 (정규화 커널) |
| `energy_bound` (6.9) | 4 | 완료 |
| `logΔ_le` (6.14), `logS_le` (6.15) | 4 | 완료 |
| `potential_le_M0` (A.9) | 4 | 완료 (`decide +kernel`, 684구간) |
| `energy_const_le` (6.4), (A.10) | 4 | 완료 (`decide +kernel`) |
| `realBound` (Prop 6.3, 점근형) | 4 | 완료 (표준 공리만) |
| `QKM_decay` | 7 | 완료 (`realBound`, `normFactor_growth`로부터) |
| `smallPrime_bound` (3.12) | 5 | 완료 (`SmallPrimeBound.lean`) |
| `inner_bound` (Prop 4.1) | 5 | 완료 (분배 공식 없이, `InnerRange.lean`) |
| `lemma42` (Lemma 4.2) | 5 | 완료 (`DetBound.lean`) |
| `outer_bound` (Prop 4.3) | 5 | 완료 (`OuterRange.lean`) |
| `big_bound` (`p > K`) | 5 | 완료 (`BigPrimes.lean`) |
| `QKM_mem_int` (Prop 5.1) | 5 | 완료 (`Integrality.lean`의 `QKM_integral`, 표준 공리만) |
| `normFactor_growth` (5.21) | 6 | `sorry` (`PrimeSum.lean`, 소수정리 의존성 결정 선행) |

## 13. 리스크

1. **논문 자체의 오류** (특히 (5.7)의 균일성). Phase 0에서는 반례를 찾지 못했다(§2).
   Prop 4.1을 포함한 §3~§5.1은 Phase 5에서 형식화되었으므로 더 이상 리스크가 아니다.
2. **소수정리 부재.** Mathlib 핀 상향과 외부 의존성 필요. 사용자 결정 사항.
3. **수치 검증의 규모.** (해결) 표 2의 684개 구간은 검증된 유리수 구간 검사기를 `decide +kernel`로
   실행해 약 280초, 최대 12.5GB 메모리로 검사된다. CI 메모리가 부족하면 청크를 더 잘게 나누면 된다.
4. **Tate 대수·연속 확장.** (해결) 내부 범위를 값 경계로 증명해 필요 없어졌다.
5. **총 규모.** 대략 1.5만~2.5만 줄의 Lean. 한 사람이 진행하면 연 단위 작업이다.
