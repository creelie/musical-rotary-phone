# verify_lemmas.jl -- the lemmas of the proofs, checked separately.
#
#  (A) S = A116470 meets [F_k, F_{k+1}) exactly in {F_k, L_{k-1}}, 4 <= k <= 400 (BigInt).
#  (B) Block decompositions, for every x <= M (default 10^6):
#        T(x) = T(F_k) + (x - F_k) + T(x - F_k)                for F_k <= x <= L_{k-1},
#        T(x) = T(L_{k-1}) + (x - L_{k-1}) + T(x - L_{k-1})    for L_{k-1} <= x <= F_{k+1},
#        Z(x) = Z(F_k) + (x - F_k) + Z(x - F_k)                for F_k <= x <= F_{k+1}.
#  (C) The values at Fibonacci numbers, k <= 400 (BigInt, from the recursions of (B)):
#        e_k = 5T(F_k) - k F_k: e_{k+1} = e_k + e_{k-2} + e_{k-3}, |e_k| <= 2F_k,
#        5Z(F_k) = k(2F_k - F_{k-1}) - 2F_k; and 6/5 < (5 - sqrt 5)/2 < 7/5.
#  (D) Records: R(j) = F_2 + F_5 + ... + F_{3j-1} satisfies 2R(j) + 1 = F_{3j+1}, and the greedy
#      representation of R(j) has exactly j terms, j <= 300 (BigInt).
#  (E) Kurkov's formula: hh(t) = parity of v_2(t + 1) gives A329320(y) = A329320(y div 2) + hh(y);
#      A329320(2^{Q+1} + z) = A329320(2^{Q+1} + 2^Q + z) = 1 + A329320(z) for z < 2^Q, Q <= 16;
#      CV(2^{P+1} + m) = 2^{P+1-pc(m)} + CV(m) for fibbinary m < 2^P, P <= 20, where CV is the
#      rewrite 0 -> 0, 01 -> 1 and pc counts ones; CV(A003714(n)) = cvZ(Zeckendorf(n)) for
#      n <= M.
# Prints "ALL OK" if every check passes.

const M = length(ARGS) >= 1 ? parse(Int, ARGS[1]) : 10^6
fails = Ref(0)
function check(c, msg)
    if !c
        fails[] += 1
        fails[] <= 20 && println("FAIL: ", msg)
    end
end

const KMAX = 1000
F = Vector{BigInt}(undef, KMAX + 1)   # F[k + 1] = F_k
L = Vector{BigInt}(undef, KMAX + 1)
F[1], F[2], L[1], L[2] = 0, 1, 2, 1
for k in 2:KMAX
    F[k+1] = F[k] + F[k-1]
    L[k+1] = L[k] + L[k-1]
end
fib(k) = F[k+1]
luc(k) = L[k+1]
S = sort(unique(vcat([fib(k) for k in 1:KMAX], [luc(k) for k in 0:KMAX])))

# (A)
for k in 4:400
    inside = filter(s -> fib(k) <= s < fib(k + 1), S)
    check(inside == [fib(k), luc(k - 1)], "S on [F_$k, F_$(k+1))")
end
println("(A) S meets [F_k, F_{k+1}) in {F_k, L_{k-1}} for 4 <= k <= 400")

# sequences up to M
Si = [Int(s) for s in S if s <= M]
Fi = [Int(fib(k)) for k in 2:60 if fib(k) <= M]
a = zeros(Int8, M + 1)   # a[n + 1] = A214973(n)
z = zeros(Int8, M + 1)   # z[n + 1] = A007895(n)
let is = 1, iff = 1
    for n in 1:M
        while is < length(Si) && Si[is+1] <= n
            is += 1
        end
        while iff < length(Fi) && Fi[iff+1] <= n
            iff += 1
        end
        a[n+1] = 1 + a[n-Si[is]+1]
        z[n+1] = 1 + z[n-Fi[iff]+1]
    end
end
Tt = zeros(Int, M + 2)   # Tt[x + 1] = T(x) = sum_{i<x} a(i)
Zt = zeros(Int, M + 2)
for x in 1:M+1
    Tt[x+1] = Tt[x] + a[x]
    Zt[x+1] = Zt[x] + z[x]
end
T(x) = Tt[x+1]
Z(x) = Zt[x+1]

# (B)
for k in 4:60
    Fk, Lk1, Fk1 = Int(fib(k)), Int(luc(k - 1)), Int(fib(k + 1))
    Fk1 > M + 1 && break
    for x in Fk:Lk1
        check(T(x) == T(Fk) + (x - Fk) + T(x - Fk), "T block 1 at x=$x")
    end
    for x in Lk1:Fk1
        check(T(x) == T(Lk1) + (x - Lk1) + T(x - Lk1), "T block 2 at x=$x")
    end
end
for k in 2:60
    Fk, Fk1 = Int(fib(k)), Int(fib(k + 1))
    Fk1 > M + 1 && break
    for x in Fk:Fk1
        check(Z(x) == Z(Fk) + (x - Fk) + Z(x - Fk), "Z block at x=$x")
    end
end
println("(B) block decompositions of T and Z hold for x <= $(M + 1)")

# (C) T(F_k), Z(F_k) in BigInt from the block recursions, matched with the direct values
TF = Dict{Int,BigInt}(1 => 0, 2 => 0, 3 => 1, 4 => 2)
ZF = Dict{Int,BigInt}(1 => 0, 2 => 0, 3 => 1)
for k in 4:399   # T(F_{k+1}) = T(L_{k-1}) + F_{k-3} + T(F_{k-3}), T(L_{k-1}) = T(F_k) + F_{k-2} + T(F_{k-2})
    TF[k+1] = TF[k] + fib(k - 2) + TF[k-2] + fib(k - 3) + TF[k-3]
end
for k in 3:399   # Z(F_{k+1}) = Z(F_k) + F_{k-1} + Z(F_{k-1})
    ZF[k+1] = ZF[k] + fib(k - 1) + ZF[k-1]
end
for k in 1:400
    if fib(k) <= M + 1
        check(TF[k] == T(Int(fib(k))) && ZF[k] == Z(Int(fib(k))), "recursion vs direct at k=$k")
    end
end
e(k) = 5 * TF[k] - k * fib(k)
for k in 1:400
    check(abs(e(k)) <= 2 * fib(k), "|e_$k| > 2F_$k")
    check(5 * ZF[k] == k * (2 * fib(k) - fib(k - 1)) - 2 * fib(k), "5Z(F_$k)")
    k >= 5 && check(e(k) == e(k - 1) + e(k - 3) + e(k - 4), "e recurrence at $k")
end
setprecision(BigFloat, 256) do
    c = (5 - sqrt(BigFloat(5))) / 2
    check(BigFloat(6) / 5 < c < BigFloat(7) / 5, "c not in (6/5, 7/5)")
end
println("(C) e_k and Z(F_k) for k <= 400; 6/5 < (5 - sqrt 5)/2 < 7/5")

# (D)
function greedy_count(n::BigInt)
    c = 0
    while n > 0
        n -= S[searchsortedlast(S, n)]
        c += 1
    end
    c
end
let R = big(0)
    for j in 0:300
        check(2R + 1 == fib(3j + 1), "2R($j) + 1")
        check(greedy_count(R) == j, "greedy count of R($j)")
        R += fib(3j + 2)
    end
end
println("(D) 2R(j) + 1 = F_{3j+1} and A214973(R(j)) = j for j <= 300")

# (E)
v2(t) = trailing_zeros(t)
hh(t) = v2(t + 1) % 2                     # = 1 - A035263(1 + t)
function a329320(y)
    top = y == 0 ? 0 : 63 - leading_zeros(y)
    sum(1 - (v2(2 * (1 + (y >> k))) % 2) for k in 0:top)
end
for y in 0:2^20
    check(a329320(y) == a329320(y >> 1) + hh(y), "A329320 recursion at $y")
end
for Q in 0:16, zz in 0:(2^Q-1)
    b = a329320(zz) + 1
    check(a329320(2^(Q + 1) + zz) == b && a329320(2^(Q + 1) + 2^Q + zz) == b, "top lemma Q=$Q z=$zz")
end
function CV(m)
    s = "0" * string(m, base = 2)
    out = Char[]
    i = 1
    while i <= length(s)
        if i < length(s) && s[i] == '0' && s[i+1] == '1'
            push!(out, '1'); i += 2
        else
            s[i] == '0' || error("not fibbinary")
            push!(out, '0'); i += 1
        end
    end
    parse(Int, String(out), base = 2)
end
isfibb(m) = (m & (m >> 1)) == 0
for P in 0:20, m in 0:(2^P-1)
    isfibb(m) || continue
    check(CV(2^(P + 1) + m) == 2^(P + 1 - count_ones(m)) + CV(m), "CV top P=$P m=$m")
end
const FI = [Int(fib(k)) for k in 0:80]   # FI[k + 1] = F_k
function zeck(n)
    out = Int[]
    while n > 0
        k = searchsortedlast(FI, n) - 1      # the largest k with F_k <= n (k >= 2 since n >= 1)
        push!(out, k)
        n -= FI[k+1]
    end
    out
end
cvZ(l) = isempty(l) ? 0 : 2^(l[1] - 2 - (length(l) - 1)) + cvZ(l[2:end])
for n in 0:M
    l = zeck(n)
    check(CV(sum(Int[2^(k - 2) for k in l]; init = 0)) == cvZ(l), "CV(A003714) = cvZ at n=$n")
end
println("(E) A329320 recursion and top lemmas, CV top lemma, CV(A003714) = cvZ for n <= $M")

if fails[] > 0
    println(fails[], " FAILURES")
    exit(1)
end
println("ALL OK")
