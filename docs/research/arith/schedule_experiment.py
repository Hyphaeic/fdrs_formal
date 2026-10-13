import itertools, math
def ext(W,q,N,k):
    a,r=divmod(k,N); return W[r]+a*q
def defects(W,q,N): return [W[m]+W[j]-ext(W,q,N,m+j) for m in range(N) for j in range(N)]
def comps(q,N):
    for cuts in itertools.combinations(range(1,q),N-1): yield (0,)+cuts
ok_unique=ok_lower=ok_upper=ok_balanced=True; total=0
for N in range(2,9):
  for q in range(N, 3*N+2):
    ceilW=tuple(math.ceil(q*k/N) for k in range(N))
    for W in comps(q,N):
      d=defects(W,q,N)
      if min(d)<0: continue
      total+=1; delta=max(d)
      if delta<=1 and W!=ceilW: ok_unique=False; print("uniq fail",N,q,W)
      if any(W[k] < math.ceil(q*k/N) for k in range(N)): ok_lower=False; print("lower fail",N,q,W)
      if any(N*W[k] > q*k + (N-1)*delta for k in range(N)): ok_upper=False; print("upper fail",N,q,W,delta)
    # balanced-word check: increments of ceilW (cyclic) are balanced
    inc=[ext(ceilW,q,N,k+1)-ext(ceilW,q,N,k) for k in range(N)]
    for L in range(1,N+1):
      sums={sum(inc[(s+i)%N] for i in range(L)) for s in range(N)}
      if max(sums)-min(sums)>1: ok_balanced=False
print("product-closed schedules checked:",total)
print("unique {1,2} = ceiling:",ok_unique,"| W >= ceil(qk/N):",ok_lower,"| N W_k <= qk+(N-1)delta:",ok_upper,"| ceiling widths balanced:",ok_balanced)
# doublings count for real moduli
for (q,N,name) in [(255,10,"25519 32-bit"),(255,5,"25519 64-bit"),(130,5,"Poly1305"),(448,8,"Ed448 64-bit"),(448,16,"Ed448 32-bit"),(521,9,"P-521 64-bit"),(521,19,"P-521 32-bit (19 limbs)"),(255,9,"25519 9 limbs"),(255,11,"25519 11 limbs"),(255,12,"25519 12 limbs")]:
    W=[math.ceil(q*k/N) for k in range(N)]
    d=defects(W,q,N); widths=[ext(W,q,N,k+1)-ext(W,q,N,k) for k in range(N)]
    print(f"{name:26s} q={q} N={N} widths={sorted(set(widths))} doubled products={sum(1 for x in d if x==1)}/{N*N}")
