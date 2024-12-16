%-----------------------------------------------------------------------------
% Copyright (C) : University of Aberdeen, Graham J.L. Kemp.
%
% Demonstration Expert System Shell (DESS)
%-----------------------------------------------------------------------------


%-----------------------------------------------------------------------------
% Backward chaining
%-----------------------------------------------------------------------------


%-----------------------------------------------------------------------------
% Use the following Quintus Prolog libraries.
%
% Library predicates actually called :-
%
% basics  : member/2
%-----------------------------------------------------------------------------
%:- ensure_loaded(library(basics)).


%-----------------------------------------------------------------------------
% Dynamic Predicates
%
% WHY(Rule)
%-----------------------------------------------------------------------------
:- dynamic why/1.


%-----------------------------------------------------------------------------
% DEDUCE(+Goal, +Why, -Outcome, -CertaintyFactor)
%
% Only called from <grammar.pl>.
%-----------------------------------------------------------------------------
deduce(Goal, Why, Outcome, CF) :-
	asserta(why(Why)),
	deduce(Goal, Outcome, CF).

deduce(_, Why, _, _) :-
	retract(why(Why)),
	!,
	fail.


%-----------------------------------------------------------------------------
% DEDUCE(+Fact, -Outcome, -CF)
%
% If Fact is in working memory, Outcome is 'YES'.
% If Fact is on RHS of a rule and all conditions are true, Outcome is 'YES'.
% Otherwise, Outcome is 'NO'.
%-----------------------------------------------------------------------------
deduce(WME, _, _) :-
	'DEBUG',
	dess_format('deduce(~p,_,_)~n', [WME]),
	fail.

deduce(fact(Fact), 'YES', CF) :-
	in_working_memory(fact(Fact)),
	wme_cf(fact(Fact), CF).

deduce(fact(Fact), 'YES', CF) :-
	\+ wme_cf(fact(Fact), _),
	bc_select_rule(fact(Fact), Rule),
	bc_solve(Rule, CF),
	(CF = 1.0 ->
		retractall(wme_cf(fact(Fact), _))
	;
		bc_fact_cf(fact(Fact), CF),
		fail
	).

deduce(fact(Fact), 'YES', CF) :-
	retract(wme_cf(fact(Fact), CF)),
	retractall(wme_cf(fact(Fact), _)),
	!.					% Prevent backtracking.

deduce(fact(_), 'NO', 1.0).


%-----------------------------------------------------------------------------
% DEDUCE(oav(+O,+A,?V), -Outcome, -CF)
%-----------------------------------------------------------------------------

% The given attribute value is stored in the given object's frame.

deduce(oav(O,A,V), 'YES', CF) :-
	nonvar(O),
	nonvar(A),
	nonvar(V),
	get_frame(oav(O,A,V), CF),
	!.


% The given attribute value is different to the known value stored in the
% given object's frame.

deduce(oav(O,A,V), 'NO', 1.0) :-
	nonvar(O),
	nonvar(A),
	nonvar(V),
	get_frame(oav(O,A,Value), _),
	Value \== 'UNKNOWN',
	!.


% No value is stored for the given object-attribute pair, but the given
% attribute value can be inferred using the current rule base.

% If the call is

deduce(oav(O,A,V), 'YES', CF) :-
	nonvar(O),
	nonvar(A),
	nonvar(V),
	bc_select_rule(oav(O,A,Expression), Rule),
	(atomic(Expression) ->
		Expression = V
	;
		true
	),
	bc_solve(Rule, CF),
	evaluate(Expression, V),
	update_frame(oav(O,A,V), CF).


% No value is stored for the given object-attribute pair.  Nor can a value be
% inferred.  However, this attribute is "askable".  Ask the user to supply a
% value, and test whether this matches the given value that we are trying to
% deduce.  If it does, reply 'YES', otherwise reply 'NO'.

deduce(oav(O,A,V), Reply, CF) :-
	nonvar(O),
	nonvar(A),
	nonvar(V),
	get_value_by_asking(O,A,UserInput,CF),
	!,
	(UserInput = V ->
		Reply = 'YES'
	;
		Reply = 'NO'
	).


% We have not been able to deduce the given value, so reply 'NO'.

deduce(oav(O,A,V), 'NO', 1.0) :-
	nonvar(O),
	nonvar(A),
	nonvar(V),
	!.


% Value(s) for the given object-attribute pair are stored in the given
% object's frame.

deduce(oav(O,A,V), V, CF) :-
	nonvar(O),
	nonvar(A),
	var(V),
	get_frame(oav(O,A,Any), _),
	Any \== 'UNKNOWN',
	!,
	(get_frame(oav(O,A,V), 1.0) ->
		CF = 1.0
	;
		get_frame(oav(O,A,V), CF)
	).


% No value is stored for the given object-attribute pair, but the attribute
% value can be inferred using the current rule base.

deduce(oav(O,A,V), Value, CF) :-
	nonvar(O),
	nonvar(A),
	var(V),
	bc_select_rule(oav(O,A,V), Rule),
	bc_solve(Rule, CF),
	evaluate(V, Value),		% Consequent may include expression:
					% "... then the <A> of <O> is <Exp>"
					% Evaluate, store and return the value
					% of this expression.
	update_frame(oav(O,A,Value), CF),
	CF = 1.0,
	!.

deduce(oav(O,A,V), V, CF) :-		% Retrieve any OAV's established by
	nonvar(O),			% the last clause.
	nonvar(A),
	var(V),
	get_frame(oav(O,A,Any), _),
	Any \== 'UNKNOWN',
	!,
	(get_frame(oav(O,A,V), 1.0) ->
		CF = 1.0
	;
		get_frame(oav(O,A,V), CF)
	).



% No value is stored for the given object-attribute pair.  Nor can a value be
% inferred.  However, this attribute is "askable".  Ask the user to supply a
% value.

deduce(oav(O,A,V), V, CF) :-
	nonvar(O),
	nonvar(A),
	var(V),
	get_value_by_asking(O,A,V,CF),
	!.


% An attribute-value pair has been given.  Return the first object found which
% has that attribute value stored in its frame.

deduce(oav(O,A,V), O, CF) :-
	var(O),
	nonvar(A),
	nonvar(V),
	get_frame(oav(O,A,V), CF),
	!.

% All other cases, reply stating that the value is 'UNKNOWN'.

deduce(oav(_,_,_), 'UNKNOWN', 1.0).


%-----------------------------------------------------------------------------
% DEDUCE(instance(+Instance, ?Class), -Outcome)
%
% If the Class is not given, but the Class of Instance is already known,
% Outcome is Class.
%-----------------------------------------------------------------------------
deduce(instance(A,B), B, CF) :-
	var(B),
	get_frame(instance(A,B), CF).

deduce(instance(A,B), B, CF) :-
	nonvar(A), nonvar(B),
	get_frame(instance(A,B), CF).

deduce(instance(A,B), 'YES', CF) :-
	nonvar(B),
	bc_select_rule(instance(A,B), Rule),
	bc_solve(Rule, CF).

deduce(instance(_,B), 'NO', 1.0) :-
	nonvar(B).

deduce(instance(A,B), B, CF) :-
	var(B),
	bc_select_rule(instance(A,B), Rule),
	bc_solve(Rule, CF),
	update_frame(instance(A,B), CF).

deduce(instance(_,B), 'NO', 1.0) :- var(B).


%-----------------------------------------------------------------------------
% DEDUCE(subclass(+InstanceOrClass, ?Class), -Outcome, -CF)
%-----------------------------------------------------------------------------
deduce(subclass(A,B), B, CF) :-
	get_frame(subclass(A,B), CF).

deduce(subclass(A,B), 'YES', CF) :-
	nonvar(B),
	bc_select_rule(subclass(A,B), Rule),
	bc_solve(Rule, CF).

deduce(subclass(_,B), 'NO', 1.0) :- nonvar(B).

deduce(subclass(A,B), B, CF) :-
	var(B),
	bc_select_rule(subclass(A,B), Rule),
	bc_solve(Rule, CF),
	update_frame(subclass(A,B), CF).

deduce(subclass(_,B), 'NO', 1.0) :- var(B).


%-----------------------------------------------------------------------------
% DEDUCE(sub_condition(+SubDisjunction), -Outcome)
%-----------------------------------------------------------------------------
deduce(sub_condition(SubDisjunction), 'YES', CF) :-
	member(Conjunction, SubDisjunction),
	bc_solve_conjunction(Conjunction, CF),
	!.

deduce(sub_condition(_), 'NO', 1.0).


%-----------------------------------------------------------------------------
% DEDUCE(comparison(+LHS, +Op, +RHS))
%-----------------------------------------------------------------------------
deduce(comparison(LHS, Op, RHS), 'YES', 1.0) :-
	evaluate(LHS, L),
	evaluate(RHS, R),
	functor(Comparison, Op, 2),
	arg(1, Comparison, L),
	arg(2, Comparison, R),
	call(Comparison).

deduce(comparison(_,_,_), 'NO', 1.0).


%-----------------------------------------------------------------------------
% BC_SOLVE(+Rule, -CertaintyFactor)
%-----------------------------------------------------------------------------
bc_solve(Rule, CF) :-
	Rule = rule(RuleName, [if(Conditions), then(Consequent)], ST),

	(dess_trace(show_chosen_rule_name) ->
		dess_format(' Trying rule: ~p~n', [RuleName])
	;
		true
	),

	asserta(why(rule(RuleName, [if(Conditions), then(Consequent)], ST))),
	member(Conjunction, Conditions),
	bc_solve_conjunction(Conjunction, CFs),
	minimum(CFs, AntecedentCF),
	Consequent = [wme(_,ConsequentCF)],
	CF is ConsequentCF * AntecedentCF,
	!,

	(dess_trace(show_chosen_rule_name) ->
		dess_format(' Rule successful: ~p~n', [RuleName])
	;
		true
	),

	retract(why(rule(RuleName, [if(Conditions), then(Consequent)], ST))).

bc_solve(Rule, _) :-
	retract(why(Rule)),
	Rule = rule(RuleName, _, _),
	(dess_trace(show_chosen_rule_name) ->
		dess_format(' Rule failed: ~p~n', [RuleName])
	;
		true
	),
	!,
	fail.


%-----------------------------------------------------------------------------
% BC_SOLVE_CONJUNCTION(+Conjunction, -CertaintyFactor)
%-----------------------------------------------------------------------------
bc_solve_conjunction([], []).

bc_solve_conjunction([H|T], [CF|CFs]) :-
	deduce(H, Outcome, CF),
	!,
	((Outcome = 'NO'; Outcome = 'UNKNOWN') ->
		fail
	;
		%update_frame(H, CF),

		% Don't want to backtrack into update_frame/2 if a subsequent
		% antecedent fails.
		%!,

		bc_solve_conjunction(T, CFs)
	).


%-----------------------------------------------------------------------------
% BC_FACT_CF(+Fact, -CF)
%-----------------------------------------------------------------------------
bc_fact_cf(Fact, NewCF) :-
	retract(wme_cf(Fact, OldCF)),
	!,
	combine_cf(OldCF, NewCF, CF),
	assert(wme_cf(Fact, CF)).

bc_fact_cf(Fact, CF) :-
	assert(wme_cf(Fact, CF)).


%-----------------------------------------------------------------------------
% GET_VALUE_BY_ASKING(+Object, +Attribute, -Value, -CF)
%-----------------------------------------------------------------------------
get_value_by_asking(O,A,V,1.0) :-
	askable(A, Prompt),
	dess_format('Frame ~p: ~p ', [O, Prompt]),
	read_line_string(Reply),
	!,
	(Reply = why ->
		respond_why,
		get_value_by_asking(O,A,V, _)
	;
		(Reply = unknown ->
			Reply = V
		;
			update_frame(oav(O,A,Reply), 1.0),
			Reply = V
		)
	).


%-----------------------------------------------------------------------------
% READ_LINE_STRING(-String)
%-----------------------------------------------------------------------------
read_line_string(String) :-
	get0(X),
	(X = 10 ->
		read_line_string(String)
	;
		read_line_string(X, Chars),
		name(String, Chars)
	).

read_line_string(10, []) :- !.
read_line_string(X, [X|Chars]) :- get0(Y),  read_line_string(Y, Chars).


%-----------------------------------------------------------------------------
% RESPOND_WHY
%-----------------------------------------------------------------------------
respond_why :-
	why(rule(RuleName, [if(Conditions), then([Consequent])], ST)),
	bind_variables_to_original_names(ST),
	dess_format('~n', []),
	show_rule_1(rule(RuleName, [if(Conditions), then([Consequent])])),
	dess_format('~n~n', []),
	!.


%-----------------------------------------------------------------------------
% CLEAR_WHY
%-----------------------------------------------------------------------------
clear_why :- retractall(why(_)).


%-----------------------------------------------------------------------------
% BIND_VARIABLES_TO_ORIGINAL_NAMES(+SymbolTable)
%-----------------------------------------------------------------------------
bind_variables_to_original_names([]).

bind_variables_to_original_names([_=Var|Others]) :-
	nonvar(Var),
	bind_variables_to_original_names(Others).

bind_variables_to_original_names([Name=Var|Others]) :-
	var(Var),
	Name=Var,
	bind_variables_to_original_names(Others).
