%-----------------------------------------------------------------------------
% Copyright (C) : University of Aberdeen, Graham J.L. Kemp.
%
% Demonstration Expert System Shell (DESS)
%-----------------------------------------------------------------------------


%-----------------------------------------------------------------------------
% Working Memory
%-----------------------------------------------------------------------------


%-----------------------------------------------------------------------------
% Dynamic Predicates
%
% WORKING_MEMORY(Element, Number Cycle)
% WME_CF(Element, CertaintyFactor)
%
% where Element = fact(Fact)
% or	Element = oav(Object,Attribute,Value)
% or	Element = instance(Instance,Class)
% or	Element = subclass(Class,SuperClass)
%-----------------------------------------------------------------------------
:- dynamic working_memory/3.
:- dynamic how/2.
:- dynamic wme_cf/2.
:- dynamic wme_number/1.


wme_number(0).


%-----------------------------------------------------------------------------
% WM
%-----------------------------------------------------------------------------
wm :-
	findall(EN,
		(	working_memory(Element,Number,_),
			EN = (Element,Number)),
		ENs),
	length(ENs, Length),
	dess_format('~p elements in working memory.~n', [Length]),
	wm(ENs).


wm([]).
wm([(Element,Number)|T]) :-
	dess_format('~` t~d ~8|: ', [Number]),
	show_rule_element(Element, _),
	show_cf(Element),
	dess_format('~n', []),
	wm(T).


show_cf(Element) :- wme_cf(Element, CF), show_cf_if_not_one(CF).

show_cf_if_not_one(CF) :-
	CF \== 1.0,
	!,
	dess_format(' with cf ~p', [CF]).
show_cf_if_not_one(_).


%-----------------------------------------------------------------------------
% SHOW_FACTS
%-----------------------------------------------------------------------------
show_facts :-
	findall(Fact, (working_memory(fact(F),_,_), Fact = fact(F)), Facts),
	show_facts(Facts).


show_facts([]).

show_facts([H|T]) :-
	show_rule_element(H, _),
	show_cf(H),
	dess_format('~n', []),
	show_facts(T).


%-----------------------------------------------------------------------------
% WME_NUMBER(?WME, ?Number)
%-----------------------------------------------------------------------------
wme_number(WME, Number) :- working_memory(WME, Number, _).


%-----------------------------------------------------------------------------
% ADD_WME(+Element, +How, +CertaintyFactor)
%-----------------------------------------------------------------------------
add_wme(Element, How, NewCF) :-
	in_working_memory(Element),
	!,
	retract(wme_cf(Element, OldCF)),
	combine_cf(OldCF, NewCF, CF),
	assert(how(Element, How)),
	assert(wme_cf(Element, CF)).

add_wme(Element, _, CF) :-
	dess_trace(show_new_wme),
	dess_format('    Adding working memory element: ', []),
	show_rule_element(Element, _),
	show_cf_if_not_one(CF),
	dess_format('~n', []),
	fail.

add_wme(Element, How, CF) :-
	next_wme_number(Number),
	fc_cycle(Cycle),
	assert(working_memory(Element, Number, Cycle)),
	assert(how(Element, How)),
	assert(wme_cf(Element, CF)).


next_wme_number(Next) :-
	retract(wme_number(Previous)),
	Next is Previous + 1,
	assert(wme_number(Next)).


%-----------------------------------------------------------------------------
% COMBINE_CF(+CFp, +CFn, -CF)
%-----------------------------------------------------------------------------
combine_cf(CFp, CFn, CF) :-
	CFp > 0,
	CFn > 0,
	CF is CFp + CFn - CFp*CFn.

combine_cf(CFp, CFn, CF) :-
	CFp < 0,
	CFn < 0,
	CF is CFp + CFn + CFp*CFn.

combine_cf(CFp, CFn, CF) :-
	abs(CFp, AbsCFp),
	abs(CFn, AbsCFn),
	minimum([AbsCFp, AbsCFn], MinAbs),
	CF is (CFp + CFn) / (1 - MinAbs).


abs(X, X) :- X >= 0.
abs(X, Y) :- X < 0, Y is -X.


%-----------------------------------------------------------------------------
% REMOVE_WME(+Element)
%-----------------------------------------------------------------------------
remove_wme(Element) :-
	dess_trace(show_new_wme),
	dess_format('    Deleting working memory element: ', []),
	show_rule_element(Element, _),
	dess_format('~n', []),
	fail.

remove_wme(Element) :-
	nonvar(Element),
	retract(working_memory(Element,_,_)),
	retract(wme_cf(Element, _)),
	(retract(how(Element, rule(_, Conditions, Actions))) ->
		retractall(fc_rule_fired(_, Conditions, Actions))
	;
		retractall(how(Element, _))
	).



%-----------------------------------------------------------------------------
% IN_WORKING_MEMORY(+Element)
%-----------------------------------------------------------------------------
in_working_memory(Element) :- working_memory(Element,_,_).


%-----------------------------------------------------------------------------
% EXPLAIN_HOW(+Element)
%-----------------------------------------------------------------------------
explain_how(Element) :-
	how(Element, 'You told me.'),
	dess_format('~nYou told me.~n~n', []).

explain_how(Element) :-
	how(Element, _),
	!,
	(	how(Element, rule(RuleName, Conjunction, _)),
		dess_format('~nBy using rule ~p and knowing:~n', [RuleName]),
		show_conjunction(Conjunction, 4),
		dess_format('~n~n', []),
		fail
	;
		true
	).

explain_how(_) :-
	dess_format('Not in working memory.~n', []).


%-----------------------------------------------------------------------------
% CLEAR_WM
%-----------------------------------------------------------------------------
clear_wm :-
	retractall(working_memory(_,_,_)),
	retractall(wme_cf(_,_)),
	retract(wme_number(_)),
	assert(wme_number(0)).

clear_how :- retractall(how(_,_)).
