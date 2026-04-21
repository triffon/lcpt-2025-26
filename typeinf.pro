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

types(Γ,X,T)             :- member((X,T),Γ).
types(Γ,app(M1,M2),Σ)    :- types(Γ,M1,fun(Ρ,Σ)),
                            types(Γ,M2,Ρ).
types(Γ,λ(X,N),fun(Ρ,Σ)) :- types([(X,Ρ)|Γ],N,Σ).

types(M,T) :- types([],M,T).
