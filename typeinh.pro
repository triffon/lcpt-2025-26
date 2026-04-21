% λ-термове
% 1. x,y,z
% 2. app(M,N)
% 3. λ(x,M)

% типове
% 1. α,β,γ
% 2. fun(ρ,τ)

% контексти
% [ (x,α), (y,fun(β,β)), .... ]

% types(+Γ,+M,?T)

:- set_prolog_flag(occurs_check,true).

i(λ(x,x)).
k(λ(x,λ(y,x))).
kstar(λ(x,λ(y,y))).
s(λ(x,λ(y,λ(z,app(app(x,z),app(y,z)))))).
ω(λ(x,app(x,x))).
c0(C0) :- kstar(C0).
c1(λ(f,λ(x,app(f,x)))).
c5(λ(f,λ(x,app(f,app(f,app(f,app(f,app(f,x)))))))).
omega(app(Omega,Omega)) :- ω(Omega).

ti(fun(α,α)).
tk(fun(α,fun(β,α))).
tkstar(fun(α,fun(β,β))).
tc(fun(fun(α,α),fun(α,α))).
ts(fun(fun(α,fun(β,γ)),fun(fun(α,β),fun(α,γ)))).

% decompose(+T, -Ρs, +A).
decompose(A, [], A).
decompose(fun(Ρ,T), [Ρ|Ρs], A) :- decompose(T, Ρs, A).

% typesall(+Γ, -Ms, +Ρs).
typesall(_,[],[]).
typesall(Γ, [M|Ms], [Ρ|Ρs]) :- types(Γ, M, Ρ), typesall(Γ, Ms, Ρs).

% compose(+X, +Ms, -N).
compose(X, [], X).
compose(X, [M|Ms], N) :- compose(app(X,M), Ms, N).

% types(+Γ,-M,+T).
types(Γ,λ(X,N),fun(Ρ,Σ)) :- types([(X,Ρ)|Γ],N,Σ).
types(Γ,N,A)             :- member((X,T),Γ),
                            % ако искаме наведнъж
                            % typesall(Γ,Ms,Ρs,X,N,A,T).

                            % нека T = fun(ρ1,fun(ρ2,...,fun(ρn,α)))
                            decompose(T,Ρs,A),

                            % търся решения на задачите types(Γ,Mi,ρi)
                            typesall(Γ,Ms,Ρs),

                            % след това задавам N = app(app(app(x,M1),M2),...,Mn)
                            compose(X,Ms,N).

types(M,T) :- types([],M,T).
