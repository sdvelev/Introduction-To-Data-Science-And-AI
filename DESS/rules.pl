%-----------------------------------------------------------------------------
% Copyright (C) : University of Aberdeen, Graham J.L. Kemp.
%
% Demonstration Expert System Shell (DESS)
%-----------------------------------------------------------------------------


%-----------------------------------------------------------------------------
% Rules
%-----------------------------------------------------------------------------


%-----------------------------------------------------------------------------
% Use the following Quintus Prolog libraries.
%
% Library predicates actually called :-
%
% strings : gensym/2
%-----------------------------------------------------------------------------
%:- ensure_loaded(library(strings)).


%-----------------------------------------------------------------------------
% Dynamic Predicates
%
% RULE_BASE(RuleName, RuleBody, Bindings)
%
% where RuleBody = [if(Conditions), then(Actions)]
% or	RuleBody = [if(Conditions), delete(Delete), add(Add)]
%-----------------------------------------------------------------------------
:- dynamic rule_base/3.


%-----------------------------------------------------------------------------
% ADD_RULE(rule(+RuleName, +RuleBody, +SymbolTable))
%-----------------------------------------------------------------------------
add_rule(rule(RuleName, RuleBody, ST)) :-
	assert(rule_base(RuleName, RuleBody, ST)).


%-----------------------------------------------------------------------------
% DELETE_RULE(+RuleName)
%-----------------------------------------------------------------------------
delete_rule(RuleName) :-
	retractall(rule_base(RuleName, _, _)).


%-----------------------------------------------------------------------------
% NEW_RULE_NAME(-RuleName)
%-----------------------------------------------------------------------------
new_rule_name(RuleName) :-
	gensym(rule_, R),
	(rule_base(R, _, _) ->
		!,
		new_rule_name(RuleName)
	;
		RuleName = R
	).


%-----------------------------------------------------------------------------
% LIST_RULES
%-----------------------------------------------------------------------------
list_rules :- rule_base(RuleName,_,_), dess_format('~p~n', [RuleName]), fail.
list_rules.


%-----------------------------------------------------------------------------
% SHOW_RULES
%-----------------------------------------------------------------------------
show_rules :-
	rule_base(RuleName,_,_),
	show_rule(RuleName),
	dess_format('~n~n', []),
	fail.

show_rules.


show_rule(RuleName) :-
	rule_base(RuleName, [if(Conditions)|Consequents], ST),

	% The rule may contain variables.  "Executing" the symbol table
	% unifies these variables with the variable names in the original
	% query text typed in by the user or loaded from a file, so that the
	% original variable names are shown when the rule is displayed.
	call_list(ST),

	show_rule_1(rule(RuleName, [if(Conditions)|Consequents])),
	!.


show_rule_1(rule(RuleName, [if(Disjunction), then(Consequents)])) :-
	dess_format('rule ~p~nif~n', [RuleName]),
	show_disjunction(Disjunction, 4),
	dess_format('~nthen~n', []),
	show_conjunction(Consequents, 4),
	dess_format('~n', []).

show_rule_1(rule(RuleName, [if(Disjunction), delete(Delete), add(Add)])) :-
	dess_format('rule ~p~nif~n', [RuleName]),
	show_disjunction(Disjunction, 4),
	dess_format('~ndelete~n', []),
	show_conjunction(Delete, 4),
	dess_format('~nadd~n', []),
	show_conjunction(Add, 4),
	dess_format('~n', []).


show_disjunction([], _).

show_disjunction([Conjunction], Indent) :-
	!,
	show_conjunction(Conjunction, Indent).

show_disjunction([Conjunction|Others], Indent) :-
	show_conjunction(Conjunction, Indent),
	TempIndent is Indent - 2,
	dess_format('~n', []),
	dess_tab(TempIndent),
	dess_format('or~n', []),
	show_disjunction(Others, Indent).


show_conjunction([], _).

show_conjunction([wme(Element, CF)], Indent) :-
	!,
	dess_tab(Indent),
	show_rule_element(Element, Indent),
	show_cf_if_not_one(CF).

show_conjunction([Element], Indent) :-
	dess_tab(Indent),
	show_rule_element(Element, Indent).

show_conjunction([wme(Element, CF)|Others], Indent) :-
	Others \== [],
	dess_tab(Indent),
	show_rule_element(Element, Indent),
	show_cf_if_not_one(CF),
	dess_format(' and~n', []),
	show_conjunction(Others, Indent).

show_conjunction([Element|Others], Indent) :-
	Others \== [],
	dess_tab(Indent),
	show_rule_element(Element, Indent),
	dess_format(' and~n', []),
	show_conjunction(Others, Indent).


show_rule_element(fact(Fact), _) :-
	dess_format('''~p''', [Fact]).

show_rule_element(oav(O,A,V), _) :-
	nonvar(O),
	get_cardinality(O,A,single),
	!,
	dess_format('the ~p of ~p is ~p', [A,O,V]).

show_rule_element(oav(O,A,V), _) :-
	nonvar(O),
	get_cardinality(O,A,multi),
	!,
	dess_format('the ~p of ~p include ~p', [A,O,V]).

show_rule_element(oav(O,A,V), _) :-
	dess_format('the ~p of ~p is ~p', [A,O,V]).

show_rule_element(instance(A,B), _) :-
	dess_format('~p is an instance of ~p', [A,B]).

show_rule_element(subclass(A,B), _) :-
	dess_format('~p is a subclass of ~p', [A,B]).

show_rule_element(sub_condition(Sub), Indent) :-
	dess_format('(~n', []),
	NewIndent is Indent + 4,
	show_disjunction(Sub, NewIndent),
	dess_format('~n', []),
	dess_tab(Indent),
	dess_format(')', []).

show_rule_element(comparison(Left,Op,Right), _) :-
	dess_format('~p ~p ~p', [Left,Op,Right]).

show_rule_element(kb_not(Sub), Indent) :-
	dess_format('not(~n', []),
	NewIndent is Indent + 4,
	show_disjunction(Sub, NewIndent),
	dess_format('~n', []),
	dess_tab(Indent),
	dess_format(')', []).

show_rule_element(remove(WME), Indent) :-
	dess_format('remove ', []),
	show_rule_element(WME, Indent).

show_rule_element(delete(WME), Indent) :-
	show_rule_element(WME, Indent).


%-----------------------------------------------------------------------------
% CLEAR_RULE_BASE
%-----------------------------------------------------------------------------
clear_rule_base :- retractall(rule_base(_,_,_)).


%-----------------------------------------------------------------------------
% FC_GET_RULE(-RuleName, -Conditions, -Actions)
%-----------------------------------------------------------------------------
fc_get_rule(RuleName, Conditions, Actions) :-
	rule_base(RuleName, [if(Conditions)|Actions], _).


%-----------------------------------------------------------------------------
% BC_SELECT_RULE(+Conclusion, -Rule)
%-----------------------------------------------------------------------------
bc_select_rule(Conclusion,
		rule(RuleName,
			[if(Conditions), then([wme(Conclusion, CF)])],
			ST)) :-
	rule_base(RuleName, [if(Conditions), then(Conclusions)], ST),
	member(wme(Conclusion, CF), Conclusions).


%-----------------------------------------------------------------------------
% CALL_LIST(+List)
%
% Each element of List should be term that can be interpreted as a goal.
% The goals are called in order. The cut in the first clause means that the
% argument can be an `incomplete' list.
%-----------------------------------------------------------------------------
call_list([]) :- !.
call_list([H|T]) :- call(H), call_list(T).


%----------------------------------------------------------------------------
% pfdm_strings.pl (used by: parser.pl; method.pl; external.pl):
%
%   concat/3    : obtained from the public library "gensym.pl".
%   gensym/2    : obtained from the public library "gensym.pl".
%   string_append/3 : public domian libraries do not have a definition for
%		      this predicate.  Even though we can define it ourselve
%		      (see below), the way this predicate is (only) used in
%		      "method.pl" suggests that it can be replaced by the
%		      P/FDM predicate "inverse_name/2" (defined in
%		      "method.pl"). The code calling "string_append/3"
%		      (dealing with Sybase) is written by Graham.
%
% 		      According to Quintus library "strings.pl",
%		      string_append/3 does the following:
%
%	% string_append(?A, ?Z, ?AZ)
%	%   is true when A, Z, and AZ are all three atoms or (Lisp) strings,
%	%   and the name of AZ is the concatenation of the names of A and Z.
%
%       JNB: Predicate "concat/3" behaves similary to this predicate if
%	     the first two arguments of "string_append/3" are instanciated.
%	     However, "string_append/3" is called at two places in "method.pl"
%	     with its first argument uninstaniated.
%----------------------------------------------------------------------------

% concat(+Name1, +Name2, -Name3)
% is like append on atoms.  That is, it appends the name of Name1 and
% the name of Name2, and binds Name3 to the atom named by the result.
% Unlike append, it will only work one way round.  Examples:
% concat(a, b, ab), concat(10, 23, 1023), concat(gs, 46, gs46).

concat(N1, N2, N3) :-
        name(N1, Ls1),    % JNB: "name/2" is a built-in predicate.
        name(N2, Ls2),
        append(Ls1, Ls2, Ls3),
        name(N3, Ls3).

% gensym(Prefix, V)
% binds V to a new atom whose name begins with Prefix and ends with a
% number.  E.g. gensym(a,X), gensym(a,Y), gensym(a,Z) might bind
% X to a1, Y to a2, Z to a3.  It only succeeds once per call, to get
% another binding for V you have to call it again.

gensym(Prefix, V) :-
        var(V),
        atomic(Prefix),
        (   retract(flag(gensym(Prefix), M))
        ;   M = 0
        ),
        N is M+1,
        asserta(flag(gensym(Prefix), N)),
        concat(Prefix, N, V),
        !.
