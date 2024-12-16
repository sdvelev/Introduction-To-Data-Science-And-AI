%-----------------------------------------------------------------------------
% Copyright (C) : University of Aberdeen, Graham J.L. Kemp.
%
% Demonstration Expert System Shell (DESS)
%-----------------------------------------------------------------------------


%-----------------------------------------------------------------------------
% Forward Chaining
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
% CONFLICT_SET(rule(RuleName, Conjunction, Consequents), AntecedentCF)
% FC_CYCLE(Cycle)
% FC_RULE_FIRED(Cycle, Conjunction, Consequents)
%
% where Consequents = [then(Actions)]
% or	Consequents = [delete(Deletes), add(Adds)]
%
% and 	Cycle is an integer
%-----------------------------------------------------------------------------
:- dynamic conflict_set/2.
:- dynamic conflict_resolution_strategy/1.
:- dynamic fc_rule_fired/3.
:- dynamic fc_cycle/1.

conflict_resolution_strategy([refractoriness, rule_ordering]).


%-----------------------------------------------------------------------------
% FC_CYCLE/1
%
% The dynamic predicate records how many forward chaining cycles have been
% carried out.  Initially, this is zero.
%-----------------------------------------------------------------------------
fc_cycle(0).


%-----------------------------------------------------------------------------
% FC
%-----------------------------------------------------------------------------
fc :-
	build_conflict_set,			% Match
	select_rule(Rule, AntecedentCF),	% Select
	fire_rule(Rule, AntecedentCF),		% Execute
	!,
	fc.

fc :-
	dess_format('~nAll applicable rules fired~n', []).


%-----------------------------------------------------------------------------
% BUILD_CONFLICT_SET
%-----------------------------------------------------------------------------
build_conflict_set :-
	fc_get_rule(RuleName, Conditions, Actions),
	member(Conjunction, Conditions),
	fc_solve(Conjunction, CFs),
	% \+ fc_rule_fired(_, Conjunction, Actions),
	minimum([1.0|CFs], AntecedentCF),
	assert(conflict_set(rule(RuleName, Conjunction, Actions), AntecedentCF)),
	fail.

build_conflict_set.


%-----------------------------------------------------------------------------
% SELECT_RULE(-Rule, -AntecedentCF)
%-----------------------------------------------------------------------------
select_rule(_, _) :-
	%
	% Refractoriness:
	%	a rule should not be allowed to fire more than once
	%	on the same data.
	%
	conflict_resolution_strategy(Strategy),
	member(refractoriness, Strategy),
	%
	% Consider each rule in the conflict set and remove those that have
	% already fired on the same data.
	%
	conflict_set(rule(RuleName, Conjunction, Actions), AntecedentCF),
	fc_rule_fired(_, Conjunction, Actions),
	retract(conflict_set(rule(RuleName, Conjunction, Actions), AntecedentCF)),
	fail.

select_rule(Rule, AntecedentCF) :-
	conflict_resolution_strategy(Strategy),
	(member(refractoriness, Strategy) ->
		select(refractoriness, Strategy, OrderingStrategy)
	;
		OrderingStrategy = Strategy
	),
	select_rule(OrderingStrategy, Rule, AntecedentCF),
	clear_conflict_set.


%select(X,[X|L],L).
%select(X,[H|T],[H|L]) :- select(X,T,L).


%-----------------------------------------------------------------------------
% SELECT_RULE(+OrderingStrategy, -Rule, -AntecedentCF)
%-----------------------------------------------------------------------------
select_rule([rule_ordering|_], Rule, AntecedentCF) :-
	conflict_set(Rule, AntecedentCF).


%-----------------------------------------------------------------------------
% FIRE_RULE(+Rule, +AntecedentCF)
%-----------------------------------------------------------------------------
fire_rule(Rule, AntecedentCF) :-
	dess_format('.', []),
	Rule = rule(RuleName, Conditions, Consequents),
	(dess_trace(show_chosen_rule_name) ->
		dess_format(' Firing rule: ~p~n', [RuleName])
	;
		true
	),
	retract(fc_cycle(Cycle)),
	assert(fc_rule_fired(Cycle, Conditions, Consequents)),
	NextCycle is Cycle + 1,
	assert(fc_cycle(NextCycle)),
	(	Consequents = [then(Actions)]
	;
		Consequents = [delete(Deletes), add(Adds)],
		append(Deletes, Adds, Actions)
	),
	perform(Actions, Rule, AntecedentCF).


%-----------------------------------------------------------------------------
% PERFORM(+Actions, +Rule, +AntecedentCF)
%
% 'Rule' is only used to provide 'how' information - it is passed as a
% parameter to add_wme/3, which asserts 'how(WME,Rule)'.
%-----------------------------------------------------------------------------
perform([], _, _).

perform([remove(WME)|Others], Rule, AntecedentCF) :-
	remove_wme(WME),
	perform(Others, Rule, AntecedentCF).

perform([delete(oav(O,A,V))|Others], Rule, AntecedentCF) :-
	remove_wme(oav(O,A,V)),
	delete_slot_value(O,A,V),
	perform(Others, Rule, AntecedentCF).

perform([delete(fact(Fact))|Others], Rule, AntecedentCF) :-
	remove_wme(fact(Fact)),
	perform(Others, Rule, AntecedentCF).

perform([wme(oav(O,A,V), ConsequentCF)|Others], Rule, AntecedentCF) :-
	CF is ConsequentCF * AntecedentCF,
	evaluate(V, Value),
	add_wme(oav(O,A,Value), Rule, CF),
	update_frame(oav(O,A,Value), CF),
	perform(Others, Rule, AntecedentCF).

perform([wme(WME, ConsequentCF)|Others], Rule, AntecedentCF) :-
	CF is ConsequentCF * AntecedentCF,
	add_wme(WME, Rule, CF),
	update_frame(WME, CF),
	perform(Others, Rule, AntecedentCF).


%-----------------------------------------------------------------------------
% FC_SOLVE(+Conjunction)
%-----------------------------------------------------------------------------
fc_solve([], []).

fc_solve([sub_condition(SubDisjunction)|T], [SubCF|CFs]) :-
	member(Sub, SubDisjunction),
	fc_solve(Sub, SubCFs),
	minimum(SubCFs, SubCF),
	!,
	fc_solve(T, CFs).

fc_solve([comparison(LHS,Op,RHS)|T], CFs) :-
	evaluate(LHS, L),
	evaluate(RHS, R),
	functor(Comparison, Op, 2),
	arg(1, Comparison, L),
	arg(2, Comparison, R),
	call(Comparison),
	!,
	fc_solve(T, CFs).

fc_solve([kb_not(SubDisjunction)|T], CFs) :-
	\+ (member(Sub, SubDisjunction), fc_solve(Sub, _)),
	!,
	fc_solve(T, CFs).

fc_solve([WME|T], [CF|CFs]) :-
	in_working_memory(WME),
	wme_cf(WME, CF),
	fc_solve(T, CFs).


%-----------------------------------------------------------------------------
% CLEAR_CONFLICT_SET
%-----------------------------------------------------------------------------
clear_conflict_set :- retractall(conflict_set(_, _)).


%-----------------------------------------------------------------------------
% MAXIMUM(+List, ?Maximum)
%-----------------------------------------------------------------------------
maximum([X|L], M) :- maximum(X, L, M).

maximum(X, [], X).
maximum(X, [Y|L], M) :- X =< Y, maximum(Y, L, M).
maximum(X, [Y|L], M) :- X > Y, maximum(X, L, M).


%-----------------------------------------------------------------------------
% MINIMUM(+List, ?Minimum)
%-----------------------------------------------------------------------------
minimum([X|L], M) :- minimum(X, L, M).

minimum(X, [], X).
minimum(X, [Y|L], M) :- X >= Y, minimum(Y, L, M).
minimum(X, [Y|L], M) :- X < Y, minimum(X, L, M).
