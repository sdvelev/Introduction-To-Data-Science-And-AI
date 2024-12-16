%-----------------------------------------------------------------------------
% Copyright (C) : University of Aberdeen, Graham J.L. Kemp.
%
% Demonstration Expert System Shell (DESS)
%-----------------------------------------------------------------------------


%-----------------------------------------------------------------------------
% Grammar for KB language
%-----------------------------------------------------------------------------


%-----------------------------------------------------------------------------
% Use the following Quintus Prolog libraries.
%
% Library predicates actually called :-
%
% basics  : member/2
% files   : file_exists/1
%-----------------------------------------------------------------------------
%:- ensure_loaded(library(basics)).
%:- ensure_loaded(library(files)).


%-----------------------------------------------------------------------------
% Use the following SICStus Prolog libraries.
%
% Library predicates actually called :-
%
% lists:   member
% system : file_exists/1
%-----------------------------------------------------------------------------

:- use_module(library(lists)).
:- use_module(library(system)).


%-----------------------------------------------------------------------------
% Dynamic Predicates
%-----------------------------------------------------------------------------
:- dynamic askable/2.
:- dynamic already_asked/2.
:- dynamic dess_trace/1.
:- dynamic noecho/0.
:- dynamic 'DEBUG'/0.
:- dynamic lexlist/1.


%-----------------------------------------------------------------------------
% KB
% KB(+Source)
%
% Top level routine, called by users.
%
% If the given source is 'user', then KB commands will be accepted from
% the keyboard.  Otherwise, Source must be the name of a file containing
% KB commands.
%
% When the fact "noecho" is asserted, the original KB commands will not be
% echoed to the screen.
%-----------------------------------------------------------------------------
kb :- kb(user).

kb(Source) :-
	((file_exists(Source); Source == user) ->
		(
			seen,
			see(Source),
			retractall(noecho),
			assert(noecho),
			read_code,
			seen
		;
			seen
		)
	;
		dess_format('kb/1: file ~p does not exist~n', [Source])
	).


%-----------------------------------------------------------------------------
% READ_CODE
%-----------------------------------------------------------------------------
read_code :-
	retractall(lexlist(_)),
	read_command(LexList),
	assert(lexlist(LexList)),
	(command(LexList, []) ->
		true
	;
		(member('<END-OF-FILE>', LexList) ->
			dess_format('Error: Missing semi-colon~n~n', [])
		;
			dess_format('Error: Invalid command: ~p~n~n',
				[LexList])
		)
	),
	!,
	\+ member('<END-OF-FILE>', LexList),
	% LexList \== ['<END-OF-FILE>'],
	read_code.


%-----------------------------------------------------------------------------
% COMMAND
%-----------------------------------------------------------------------------

command --> [help], { show_help }.
command --> [exit], { halt }.

command --> [trace], integer_list(Options), { trace_options(Options) }.

command --> [strategy], integer_list(Options), { strategy_options(Options) }.

command --> frame.

command --> rule(Rule), { add_rule(Rule) }.

command -->
	[the], [Attribute], [of], [Object], is_or_includes,
	known_value(Value, _),
	{	\+ kb_variable(Object),
		var(Value),
		(	get_frame(oav(Object, Attribute, X), CF),
			dess_format('~p', [X]),
			show_cf_if_not_one(CF),
			dess_format('~n', []),
			fail
		;
			true
		)
	}.

command -->
	[the], [Attribute], [of], [Object], is_or_includes,
	known_value(Value, _),
	{	kb_variable(Object),
		\+ kb_variable(Value),
		(	get_frame(oav(X, Attribute, Value), CF),
			dess_format('~p', [X]),
			show_cf_if_not_one(CF),
			dess_format('~n', []),
			fail
		;
			true
		)
	}.

command -->
	[the], [Attribute], [of], [Object], [is], known_value(Value, _),
	with_cf(CF),
	{	\+ kb_variable(Object),
		\+ kb_variable(Value),
		update_frame(oav(Object, Attribute, Value), CF),
		add_wme(oav(Object, Attribute, Value), 'You told me.', CF)
	}.

command -->
	[the], [Attribute], [of], [Object], [include], known_value(Value, _),
	with_cf(CF),
	{	\+ kb_variable(Object),
		\+ kb_variable(Value),
		(	get_cardinality(Object, Attribute, multi);
			put_cardinality(Object, Attribute, multi)
		),
		update_frame(oav(Object, Attribute, Value), CF),
		add_wme(oav(Object, Attribute, Value), 'You told me.', CF)
	}.

command --> fact(Fact), with_cf(CF), { add_wme(Fact, 'You told me.', CF) }.

command --> [add], [frame], [Frame], { add_frame_to_wm(Frame) }.

command --> [remove], integer_list(Ns),
		{	member(N,Ns),
			wme_number(WME, N),
			remove_wme(WME),
			fail
			;
			true
		}.

command --> [remove], wm_element(WME, _), { remove_wme(WME) }.


command --> [askable], [Attribute], [string(Prompt)],
		{ assert(askable(Attribute, Prompt)) }.

command --> [load], [string(File)], { kb(File) }.


command --> [wm], { wm }.

command --> [show], [facts], { show_facts }.

command --> [list], [frames], { list_frames }.
command --> [show], [frames], { show_frames }.
command --> [show], [frame], [Frame], { show_frame(Frame) }.
command --> [delete], [frame], [Frame], { delete_frame(Frame) }.

command --> [list], [rules], { list_rules }.
command --> [show], [rules], { show_rules }.
command --> [show], [rule], [Rule], { show_rule(Rule) }.
command --> [delete], [rule], [Rule], { delete_rule(Rule) }.

command --> [how], [N], { integer(N), wme_number(WME, N), explain_how(WME) }.
command --> [how], wm_element(WME, _), { explain_how(WME) }.

command -->
	deduce_or_bc, wm_element(WME, _),
	{	clear_why,
		deduce(WME, '<top-level request>', Outcome, CF),
		dess_format('~p', [Outcome]),
		show_cf_if_not_one(CF),
		dess_format('~n', []),
		CF = 1.0
		;
		true
	}.

command --> [fc], { fc }.

command --> [clear], { clear }.

command --> ['<END-OF-FILE>'].

command --> [].


deduce_or_bc --> [deduce].
deduce_or_bc --> [bc].

%-----------------------------------------------------------------------------
% FRAME
%-----------------------------------------------------------------------------
frame --> [X], [instance], [of], [Y], slots(Slots),
		{ add_frame(X, instance_of, Y, Slots) }.

frame --> [X], [subclass], [of], [Y], slots(Slots),
		{ add_frame(X, subclass_of, Y, Slots) }.


%-----------------------------------------------------------------------------
% SLOTS(-Slots)
%-----------------------------------------------------------------------------
slots([Slot|Slots]) --> [with], slot(Slot), other_slots(Slots).
slots([]) --> [].


slot(slot(SlotName, Facets)) -->
	[SlotName], [':'], ['['], facets(Facets), [']'].

slot(slot(SlotName, [cardinality(multi)|Values])) -->
	[SlotName], [':'], ['['], slot_values(Values), [']'].

slot(slot(SlotName, [value(Value, 1.0)])) --> [SlotName], [':'], [Value].


other_slots([Slot|Slots]) --> slot(Slot), other_slots(Slots).
other_slots([]) --> [].


facets([value(Value, 1.0)|Facets]) -->
	[value], [':'], [Value], other_facets(Facets).

facets([cardinality(Cardinality)|Facets]) -->
	[cardinality], [':'], [Cardinality], other_facets(Facets).

facets([when_accessed(Rule)|Facets]) -->
	[when_accessed], [':'], rule(Rule), other_facets(Facets).


other_facets(Facets) --> [','], facets(Facets).
other_facets([]) --> [].


slot_values([value(Value,1.0)|Values]) --> [Value], other_slot_values(Values).

other_slot_values(Values) --> [','], slot_values(Values).
other_slot_values([]) --> [].


%-----------------------------------------------------------------------------
% RULE(-Rule)
%-----------------------------------------------------------------------------
rule(rule(RuleName, [if(Conditions), delete(Delete), add(Add)], ST)) -->
	[rule], [RuleName],
	[if], conditions(Conditions, ST),
	[delete], rule_delete(Delete, ST),
	[add], rule_add(Add, ST).

rule(rule(RuleName, [if(Conditions), delete([]), add(Add)], ST)) -->
	[rule], [RuleName],
	[if], conditions(Conditions, ST),
	[add], rule_add(Add, ST).

rule(rule(RuleName, [if(Conditions), delete(Delete), add([])], ST)) -->
	[rule], [RuleName],
	[if], conditions(Conditions, ST),
	[delete], rule_delete(Delete, ST).

rule(rule(RuleName, [if(Conditions), then(Actions)], ST)) -->
	[rule], [RuleName],
	mustbe([if]), conditions(Conditions, ST),
	mustbe([then]), actions(Actions, ST).

rule(rule(RuleName, [if(Conditions), then(Actions)], ST)) -->
	[if], conditions(Conditions, ST),
	mustbe([then]), actions(Actions, ST),
	{ new_rule_name(RuleName) }.


%-----------------------------------------------------------------------------
% CONDITIONS(-Conditions, +SymbolTable)
%-----------------------------------------------------------------------------
conditions([C|Cs], ST) -->
	cond_term(C, ST),
	conditions_rest(Cs, ST).

conditions_rest([C|Cs], ST) -->
	[or],
	cond_term(C, ST),
	conditions_rest(Cs, ST).

conditions_rest([], _) --> [].


cond_term([C|Cs], ST) --> mustbe(condition(C, ST)), cond_term_rest(Cs, ST).

cond_term_rest([C|Cs], ST) -->
	[and],
	mustbe(condition(C, ST)),
	cond_term_rest(Cs, ST).

cond_term_rest([], _) --> [].


%-----------------------------------------------------------------------------
% CONDITION(-Condition, +SymbolTable)
%-----------------------------------------------------------------------------
condition(kb_not(Sub), ST) --> [not], ['('], conditions(Sub, ST), [')'].
condition(sub_condition(Sub), ST) --> ['('], conditions(Sub, ST), [')'].
condition(Condition, ST) --> wm_element(Condition, ST).
condition(Condition, ST) --> comparison(Condition, ST).


%-----------------------------------------------------------------------------
% RULE_DELETE(-DeleteItems, +ST)
%-----------------------------------------------------------------------------
rule_delete([delete(WME)|WMEs],ST) -->
	wm_element(WME,ST),
	rule_delete_rest(WMEs,ST).

rule_delete_rest(Others, ST) --> [and], rule_delete(Others, ST).
rule_delete_rest([], _) --> [].


%-----------------------------------------------------------------------------
% RULE_ADD(-DeleteItems, +ST)
%
% Exactly the same as rule_delete/4 - ought to rationalise.
%-----------------------------------------------------------------------------
rule_add([wme(WME, 1.0)|Others],ST) -->
	wm_element(WME,ST),
	rule_add_rest(Others,ST).

rule_add_rest(Others, ST) --> [and], rule_add(Others, ST).
rule_add_rest([], _) --> [].


%-----------------------------------------------------------------------------
% WM_ELEMENT(-WME, +ST)
%-----------------------------------------------------------------------------
wm_element(WME, _)  --> fact(WME).
wm_element(WME, ST) --> frame_access(WME, ST).
wm_element(WME, ST) --> instance_relationship(WME, ST).
wm_element(WME, ST) --> subclass_relationship(WME, ST).


%-----------------------------------------------------------------------------
% FACT(-Fact)
%-----------------------------------------------------------------------------
fact(fact(Fact)) --> [string(Fact)].


%-----------------------------------------------------------------------------
% FRAME_ACCESS(-OAV, +SymbolTable)
%-----------------------------------------------------------------------------
frame_access(oav(Object, Attribute, Variable), ST) -->
	[the], [Attribute], [of], [ObjectId], is_or_includes,
	arith_expr(Variable, ST),
	{	kb_variable(ObjectId),
		member(ObjectId=Object, ST),	% Object is a new variable.
		!
	}.

frame_access(oav(Object, Attribute, Value), ST) -->
	[the], [Attribute], [of], [ObjectId], is_or_includes,
	arith_expr(Value, ST),
	{ 	nonvar(Value),
		\+ kb_variable(Value),
		kb_variable(ObjectId),
		member(ObjectId=Object, ST),	% Object is a new variable.
		!
	}.

frame_access(oav(Object, Attribute, Variable), ST) -->
	[the], [Attribute], [of], [Object], is_or_includes,
	arith_expr(Variable, ST),
	{	\+ kb_variable(Object),
		!
	}.

frame_access(oav(Object, Attribute, Value), ST) -->
	[the], [Attribute], [of], [Object], is_or_includes,
	arith_expr(Value, ST),
	{	\+ kb_variable(Object),
		\+ kb_variable(Value)
	}.


%-----------------------------------------------------------------------------
% IS_OR_INCLUDES
%-----------------------------------------------------------------------------
is_or_includes --> [is].
is_or_includes --> [include].


%-----------------------------------------------------------------------------
% SUBCLASS_RELATIONSHIP(-Subclass, +SymbolTable)
%-----------------------------------------------------------------------------
subclass_relationship(subclass(Frame, Y), ST) -->
	[X], [is], [a], [subclass], [of], [Y],
	{	kb_variable(X),
		\+ kb_variable(Y),
		member(X=Frame, ST)		% Frame is a new variable.
	}.

subclass_relationship(subclass(X, Frame), ST) -->
	[X], [is], [a], [subclass], [of], [Y],
	{	\+ kb_variable(X),
		kb_variable(Y),
		member(Y=Frame, ST)		% Frame is a new variable.
	}.

subclass_relationship(subclass(X, Y), _) -->
	[X], [is], [a], [subclass], [of], [Y],
	{ \+ kb_variable(X) }.


%-----------------------------------------------------------------------------
% INSTANCE_RELATIONSHIP(+Instance, +SymbolTable)
%-----------------------------------------------------------------------------
instance_relationship(instance(Frame, Y), ST) -->
	[X], [is], [an], [instance], [of], [Y],
	{	kb_variable(X),
		\+ kb_variable(Y),
		member(X=Frame, ST)		% Frame is a new variable.
	}.

instance_relationship(instance(X, Frame), ST) -->
	[X], [is], [an], [instance], [of], [Y],
	{	\+ kb_variable(X),
		kb_variable(Y),
		member(Y=Frame, ST)		% Frame is a new variable.
	}.

instance_relationship(instance(X, Y), _) -->
	[X], [is], [an], [instance], [of], [Y],
	{ \+ kb_variable(X) }.


%-----------------------------------------------------------------------------
% ACTIONS(-Actions, +SymbolTable)
%-----------------------------------------------------------------------------
actions([A|As], ST) --> action(A, ST), other_actions(As, ST).

other_actions([A|As], ST) --> [and], action(A, ST), other_actions(As, ST).
other_actions([], _) --> [].

action(wme(WME, CF), ST) --> wm_element(WME, ST), with_cf(CF).
action(remove(Action), ST) --> [remove], mustbe(wm_element(Action, ST)).


%-----------------------------------------------------------------------------
% WITH_CF(-CertaintyFactor)
%-----------------------------------------------------------------------------
with_cf(CF)  --> [with], [cf], ['-'], [X], {CF is 0 - X}.
with_cf(CF)  --> [with], [cf], [CF].
with_cf(1.0) --> [].


%-----------------------------------------------------------------------------
% COMPARISON(-Comparison, +ST)
%-----------------------------------------------------------------------------
comparison(comparison(Expr1, Operator, Expr2), ST) -->
	arith_expr(Expr1, ST),
	comparison_operator(Operator),
	mustbe(arith_expr(Expr2, ST)).


%-----------------------------------------------------------------------------
% COMPARISON_OPERATOR(-Operator)
%-----------------------------------------------------------------------------
comparison_operator('\\==') --> ['<'], ['>'].
comparison_operator('=<') --> ['='], ['<'].
comparison_operator('>=') --> ['>'], ['='].
comparison_operator('=') --> ['='].
comparison_operator('<') --> ['<'].
comparison_operator('>') --> ['>'].


%-----------------------------------------------------------------------------
% KNOWN_VALUE(-Value, +ST)
%
% ST is not needed?
%-----------------------------------------------------------------------------
known_value(Value, ST) -->
	arith_expr(Expression, ST),
	{ evaluate(Expression, Value) }.


%-----------------------------------------------------------------------------
% ARITH_EXPR(-ArithExpr, +ST)
%-----------------------------------------------------------------------------
arith_expr(Expression, ST) -->
	arith_term(Term, ST),
	arith_expr_rest(Term, Expression, ST).


arith_expr_rest(Term1, Expression, ST) -->
	['+'], mustbe(arith_term(Term2, ST)),
	arith_expr_rest('+'(Term1, Term2), Expression, ST).

arith_expr_rest(Term1, Expression, ST) -->
	['-'], mustbe(arith_term(Term2, ST)),
	arith_expr_rest('-'(Term1, Term2), Expression, ST).

arith_expr_rest(Term, Term, _) --> [].


%-----------------------------------------------------------------------------
% ARITH_TERM(-ArithTerm, +ST)
%-----------------------------------------------------------------------------
arith_term(ArithTerm, ST) -->
	arith_fac(ArithFac, ST),
	arith_term_rest(ArithFac, ArithTerm, ST).


arith_term_rest(Factor1, Expression, ST) -->
	['*'], mustbe(arith_fac(Factor2, ST)),
	arith_term_rest('*'(Factor1, Factor2), Expression, ST).

arith_term_rest(Factor1, Expression, ST) -->
	['/'], mustbe(arith_fac(Factor2, ST)),
	arith_term_rest('/'(Factor1, Factor2), Expression, ST).

arith_term_rest(Factor, Factor, _) --> [].


%-----------------------------------------------------------------------------
% ARITH_FAC(-ArithFac, +ST)
%-----------------------------------------------------------------------------
arith_fac(V, ST) --> ['('], arith_expr(V, ST), [')'].

arith_fac(V, ST) -->
	[Variable],
	{ kb_variable(Variable), member(Variable=V, ST), ! }.

arith_fac(ask(Prompt), _) --> [ask], [string(Prompt)], !.

arith_fac(V, _) --> [V].


%-----------------------------------------------------------------------------
% INTEGER_LIST(-Integers)
%-----------------------------------------------------------------------------
integer_list([X|Xs]) --> optional_comma, [X], { integer(X) }, integer_list(Xs).
integer_list([]) --> [].


optional_comma --> [','].
optional_comma --> [].


%-----------------------------------------------------------------------------
% MUSTBE(+Symbol)
%
% Symbol :  The name of the phrase which we require to be found here.
%
% Called whenever Symbol must be recognised here if the parse is to succeed.
% If Symbol is found then MUSTBE succeeds, else report an error, close any
% open source file and terminate parsing.
%
% PW 01.12.92
%-----------------------------------------------------------------------------
mustbe(Symbol) -->
	Symbol, ! ;
	error_report(syntax, Symbol).


%-----------------------------------------------------------------------------
% ERROR_REPORT(+Error_type, +Argument, +Remaining_input, [])
%
% Error_type:  Nature of error, i.e. syntactic or semantic.
% Argument:  Contains a description of the error.
% Remaining_input :  The unparsed portion of the lexlist.
%
% Displays correctly parsed portion of the lexlist, a message reporting that
% parsing has failed here for reasons contained in Argument and the
% remaining, unparsed portion of the lexlist.  Close any source file and
% abort.
%
% PW 01.12.92
% Modified, GJLK.
%-----------------------------------------------------------------------------
error_report(syntax, Expected, RemainingInput, []) :-
	dess_format('~nSyntax error~n~n', []),
	expected_token(Expected, Token),
	dess_format('"~p" expected.~n~n', [Token]),
	show_where(RemainingInput).

error_report(semantic, Message, RemainingInput, []) :-
	dess_format('~n', []),
	write_list(Message),
	dess_format('~n', []),
	show_where(RemainingInput).


show_where(RemainingInput) :-
	retract(lexlist(Lexlist)),
	append(ParsedInput, RemainingInput, Lexlist),
	write_list(ParsedInput),
	dess_format('<<here>>~n', []),
	write_list(RemainingInput),
	dess_format('~n', []),
	seen,
	!,
	fail.


expected_token([Token], Token) :- !.
expected_token(Expected, Token) :- functor(Expected, Token, _).


write_list([])    :- dess_format('~n', []).
write_list([H|T]) :- dess_format('~p ', [H]), write_list(T).


%-----------------------------------------------------------------------------
% Support predicates.
%-----------------------------------------------------------------------------
kb_variable('?').
kb_variable(X) :- name(X, [First|_]), (is_upper(First); First=63).


%-----------------------------------------------------------------------------
% EVALUATE(+Expression, ?Value)
%-----------------------------------------------------------------------------
evaluate(X, X) :- var(X).
evaluate(X, X) :- nonvar(X), atomic(X), !.
evaluate(X, _) :- nonvar(X), atomic(X), !, fail.
evaluate(ask(Prompt),Reply) :- evaluate_ask(Prompt, Reply), !.
evaluate(Expression, Value) :- Value is Expression.


evaluate_ask(Prompt, Reply) :- already_asked(Prompt, Reply), !.
evaluate_ask(Prompt, Reply) :-
	dess_format('~p ',[Prompt]),
	read_line_string(Reply),
	assertz(already_asked(Prompt, Reply)).


%-----------------------------------------------------------------------------
% SHOW_HELP
%-----------------------------------------------------------------------------
show_help :-
	dess_format('~nDESS Commands~n', []),
	dess_format('-------------~n', []),
	dess_format('    load "<File>";~n', []),
	dess_format('    "<fact>";~n', []),
	dess_format('    show facts;~n', []),
	dess_format('    rule <RuleName> if <Conditions> then <Conclusions>;~n', []),
	dess_format('    list rules;~n', []),
	dess_format('    show rules;~n', []),
	dess_format('    show rule <RuleName>;~n', []),
	dess_format('    wm;~n', []),
	dess_format('    fc;~n', []),
	dess_format('    deduce <working memory element>;~n', []),
	dess_format('    how <working memory element>;~n', []),
	dess_format('    remove <working memory element>;~n', []),
	dess_format('    the <Attribute> of <Object> is <Value>;~n', []),
	dess_format('    askable <Attribute> <Prompt>;~n', []),
	dess_format('    clear;~n', []),
	dess_format('    trace [<numbers>];~n', []),
	dess_format('    help;~n', []),
	dess_format('    exit;~n~n', []).


%-----------------------------------------------------------------------------
% TRACE_OPTIONS(+Options)
%-----------------------------------------------------------------------------
trace_options([]) :-
	show_trace_options.

trace_options([Number|Numbers]) :-
	trace_option(Number, Option, _),
	(dess_trace(Option) ->
		retract(dess_trace(Option))
	;
		assert(dess_trace(Option))
	),
	trace_options(Numbers).


trace_option(1, show_chosen_rule_name, 'Show the name of the chosen rule').
trace_option(2, show_new_wme, 'Show new working memory elements').


show_trace_options :-
	dess_format('~nTrace options~n-------------~n', []),
	trace_option(Number, OptionToken, OptionText),
	dess_format('~` t~d ~8|: ~p', [Number, OptionText]),
	(dess_trace(OptionToken) ->
		dess_format(' [on]~n', [])
	;
		dess_format(' [off]~n', [])
	),
	fail.

show_trace_options :- dess_format('~n', []).


%-----------------------------------------------------------------------------
% STRATEGY_OPTIONS(+Options)
%-----------------------------------------------------------------------------
strategy_options([]) :-
	!,
	show_strategy_options.


strategy_options(Numbers) :-
	clear_strategy,
	findall(Option,
		(	member(X, Numbers),
			strategy_option(X, Option,_)
		), Options),
	new_strategy(Options).

strategy_option(1, refractoriness, 'Refractoriness').
strategy_option(2, rule_ordering, 'Rule ordering').
strategy_option(3, recency, 'Recency').
strategy_option(4, specificity, 'Specificity').

show_strategy_options :-
	dess_format('~nConflict resolution strategy options~n', []),
	dess_format('------------------------------------~n', []),
	strategy_option(Number, _, OptionText),
	dess_format('~` t~d ~8|: ~p~n', [Number, OptionText]),
	fail.

show_strategy_options :-
	dess_format('~n', []),
	conflict_resolution_strategy(Strategy),
	dess_format('Current strategy: ~p~n~n', [Strategy]).


%-----------------------------------------------------------------------------
% CLEAR
%-----------------------------------------------------------------------------
clear :-
	clear_wm,
	clear_rule_base,
	retractall(frame(_,_,_,_)),
	retractall(conflict_set(_)),
	retractall(fc_rule_fired(_,_,_)),
	retractall(askable(_,_)),
	clear_why,
	clear_how.


%-----------------------------------------------------------------------------
% DESS_FORMAT(+FormatString, +Arguments)
%-----------------------------------------------------------------------------
dess_format(FormatString, Arguments) :-
	format(FormatString, Arguments),
	current_output(Output),
	flush_output(Output).


%-----------------------------------------------------------------------------
% DESS_TAB(+Indent)
%-----------------------------------------------------------------------------
dess_tab(0).

dess_tab(Indent) :-
	Indent > 0,
	dess_format(' ', []),
	NewIndent is Indent - 1,
	dess_tab(NewIndent).
