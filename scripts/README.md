# scripts — Phase 0 수치 검증

`PLAN.md` §2(Phase 0)의 검증 스크립트. 식 번호는 `ZETA5_IS_IRRATIONAL.pdf`를 따른다.
의존성은 각 스크립트 머리의 PEP 723 블록에 있으므로 `uv run`으로 바로 실행된다.

```bash
uv run scripts/check_constants.py     # §5, 부록 B의 유리수 상수            (<1초)
uv run scripts/check_potential.py     # 부록 A: Lemma 6.1, 표 1·2, (A.9)     (~7초)
uv run scripts/check_functionals.py   # μ_X, τ_X 정의: Prop 2.2, (3.1)-(3.7)  (~90초)
uv run scripts/check_local.py         # Δ_K(X): §3-§4 p-진, §6 실수 (K=40,80,120, ~30초)
uv run scripts/check_prime_sum.py     # 허용 (K, M)에서 m_{K,M}, (5.7), (5.11) (K=320000, ~8초)
```

`zeta5_defs.py`는 §2, §5 대상(μ_X, G_K, Δ_K, S_K, v_p(S_K) 등)의 정확한 유리수 참조 구현이다.
Phase 1의 Lean 정의를 작은 경우에 대조할 때 이 값을 쓴다.

큰 K는 오래 걸린다. Δ_K 계산 시간은 n = 1..7 (K = 40n)에 대해 대략 0.1초, 3초, 25초, 2분, 5분,
13분, 30분 이상이다. `--cache DIR`을 주면 정확한 다항식을 저장해 재사용한다.

```bash
uv run scripts/check_local.py 1 2 3 4 5 6 7 --cache /tmp/zeta5-cache
uv run scripts/check_local.py 10 20 --inner-only       # Prop 4.1 성분별 검사만 (행렬식 없이)
uv run scripts/check_prime_sum.py 8000000 200          # M = 200의 최소 허용 K (~40분)
```

결과 요약은 `PLAN.md` §2에 있다.
