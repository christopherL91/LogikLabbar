boxrow(Proofs, Line, Conclusion, Rule) :- 
	member(P, Proofs), 
	(
		P = [[_|_]|_] -> row(P, Line, Conclusion, Rule);
		P = [Line,Conclusion,Rule]
	).
row(Proofs, Line, Conclusion, Rule) :- member(P,Proofs), P = [Line,Conclusion,Rule].
invalid_assumption([H|Tail]) :- 
	H = [[_|_]|Tail1] -> invalid_assumption(Tail1); 
	H = [_,_,assumption], !;
	invalid_assumption(Tail).
reverseboxes(X,X) :- not(is_list(X)).
reverseboxes([],[]).
reverseboxes([Elem|Rest], [Out|Tail]) :- 
	(Elem = [[_|_]|_] -> reverse(Elem, R); Elem = R),
	reverseboxes(R,Out), reverseboxes(Rest,Tail), !. 

reverserecursive(List,Out) :- reverse(List,Reversed), reverseboxes(Reversed,Out), !. 


valid_rule(assumption,_,_,_).
valid_rule(copy(RX),X,Proofs,_) :- row(Proofs,RX,X,_).
valid_rule(andint(RX,RY),and(X,Y),Proofs,_) :- row(Proofs, RX,X,_), row(Proofs, RY, Y,_).
valid_rule(andel1(RX),X,Proofs,_) :- row(Proofs, RX, and(X,_), _).
valid_rule(andel2(RX),Y,Proofs,_) :- row(Proofs, RX, and(_,Y), _).
valid_rule(orint1(RX),or(X,_),Proofs,_) :- row(Proofs, RX, X, _).
valid_rule(orint2(RX),or(_,X),Proofs,_) :- row(Proofs, RX, X, _).
valid_rule(orel(RX,RY,RU,RV,RW),Result,Proofs,_) :-
	RY =< RU,
	RV =< RW,
	row(Proofs, RX, or(X,Y), _), 
	boxrow(Proofs, RY, X, _),
	boxrow(Proofs, RU, Result, _), 
	boxrow(Proofs, RV, Y, _),
	boxrow(Proofs, RW, Result, _).
valid_rule(impint(RX,RY),imp(X,Y),Proofs,_) :-
	Y = X; 
	RX =< RY,
	boxrow(Proofs, RX, X, assumption),
	boxrow(Proofs, RY, Y, Rule2),
	invalid_last_rule(Rule2).
valid_rule(impel(RX,RY), Y, Proofs, _) :-
	row(Proofs, RX, X, _),
	row(Proofs, RY, imp(X,Y),_).
valid_rule(negint(RX,RY), neg(X), Proofs, _) :- 
	RX =< RY,
	boxrow(Proofs, RX, X, _),
	boxrow(Proofs, RY, cont, _).
valid_rule(negel(RX,RY), cont, Proofs, _) :-
	row(Proofs, RX, X, _),
	row(Proofs, RY, neg(X), _).
valid_rule(contel(RX), _, Proofs, _) :- 
	row(Proofs, RX, cont, _).
valid_rule(negnegint(RX), neg(neg(X)), Proofs, _) :- 
	row(Proofs, RX, X, _).
valid_rule(negnegel(RX), X, Proofs, _) :- 
	row(Proofs, RX, neg(neg(X)), _).
valid_rule(mt(RX,RY), neg(X), Proofs, _) :-
	row(Proofs, RX, imp(X,Y), _),
	row(Proofs, RY, neg(Y), _).
valid_rule(pbc(RX,RY), X, Proofs, _) :-
	RX =< RY,
	boxrow(Proofs, RX, neg(X), _),
	boxrow(Proofs, RY, cont, _).
valid_rule(lem, or(X,neg(X)), _, _).
valid_rule(lem, or(neg(X),X), _, _).
valid_rule(premise,X,_,Prems) :- member(X,Prems).

invalid_last_rule(Rule) :- not(member(Rule, [lem,assumption])).

check_proof(_, []).
check_proof(Prems, [P|Proofs]) :- 
	P = [[X|XS]|Rest] -> append([[X|XS]|Rest],Proofs,Flattened), check_proof(Prems, Flattened), !; 
	P = [_, Goal, Rule], valid_rule(Rule, Goal, Proofs, Prems), check_proof(Prems, Proofs), !.


valid_proof(Prems, Goal, Proof) :- 
	not(invalid_assumption(Proof)),
	reverserecursive(Proof,[P|Rest]), 
	P = [_, Goal, Rule],
	valid_rule(Rule, Goal, Rest, Prems), 
	check_proof(Prems,Rest), !.

verify(InputFileName) :- see(InputFileName),
						read(Prems), read(Goal), read(Proof),
						seen,
						valid_proof(Prems, Goal, Proof).