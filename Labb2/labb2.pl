row(S,L,Ls) :- member(X,L), X = [S,Ls].

verify(Input) :-
see(Input), read(T), read(L), read(S), read(F), seen, check(T,L,S,[],F).

% check(T, L, S, U, F)
% T - The transitions in form of adjacency lists
% L - The labeling
% S - Current state
% U - Currently recorded states
% F - CTL Formula to check.

%p
check(_, L, S, [], F) :- row(S,L,Ls), member(F,Ls).

%neg p
check(_,L,S,[],neg(F)) :- row(S,L,Ls), not(member(F,Ls)).

%and
check(T,L,S,[],and(F,G)) :- check(T,L,S,[],F), check(T,L,S,[],G).

%or1
check(T,L,S,[],or1(F,_)) :- check(T,L,S,[],F).
check(T,L,S,[],or2(_,G)) :- check(T,L,S,[],G).
check(T,L,S,[],or(F,G)) :- check(T,L,S,[],or1(F,G));check(T,L,S,[],or2(F,G)).

%AX
check(T,L,S,[],ax(F)) :- row(S,T,Ts), forall(member(X,Ts),check(T,L,X,[],F)).

%AG
check(_,_,S,U,ag1(_)) :- member(S,U).
check(T,L,S,U,ag2(F)) :- not(member(S,U)),
						check(T,L,S,[],F),
						append(U,[S],Us),
						row(S,T,Ts),
						forall(
							member(X,Ts),
							check(T,L,X,Us,ag(F))
						).
check(T,L,S,U,ag(F)) :- check(T,L,S,U,ag1(F)); check(T,L,S,U,ag2(F)).

%AF
check(T,L,S,U,af1(F)) :- not(member(S,U)), check(T,L,S,[],F).
check(T,L,S,U,af2(F)) :- not(member(S,U)),
						append(U,[S],Us),
						row(S,T,Ts),
						forall(
							member(X,Ts),
							check(T,L,X,Us,af(F))
						).
check(T,L,S,U,af(F)) :- check(T,L,S,U,af1(F)); check(T,L,S,U,af2(F)).

%EX
check(T,L,S,[],ex(F)) :- row(S,T,Ts),
						member(X,Ts),
						check(T,L,X,[],F).

%EG
check(_,_,S,U,eg1(_)) :- member(S,U).
check(T,L,S,U,eg2(F)) :- not(member(S,U)),
						 check(T,L,S,[],F),
						 row(S,T,Ts),
						 append(U,[S],Us),
						 member(X,Ts),
						 check(T,L,X,Us,eg(F)).
check(T,L,S,U,eg(F)) :- check(T,L,S,U,eg1(F)); check(T,L,S,U,eg2(F)).
%EF
check(T,L,S,U,ef1(F)) :- not(member(S,U)), check(T,L,S,[],F).
check(T,L,S,U,ef2(F)) :- not(member(S,U)),row(S,T,Ts),append(U,[S],Us),member(X,Ts),check(T,L,X,Us,ef(F)).
check(T,L,S,U,ef(F)) :- check(T,L,S,U,ef1(F));check(T,L,S,U,ef2(F)).