%-----------------------------------------------------------------------------
% Copyright (C) : University of Aberdeen, Graham J.L. Kemp.
%
% Demonstration Expert System Shell (DESS)
%-----------------------------------------------------------------------------


%-----------------------------------------------------------------------------
% Frames
%-----------------------------------------------------------------------------


%-----------------------------------------------------------------------------
% Use the following Quintus Prolog libraries.
%
% Library predicates actually called :-
%
% basics  : member/2
% lists   : delete/3, remove_dups/2
%-----------------------------------------------------------------------------
%:- ensure_loaded(library(basics)).
%:- ensure_loaded(library(lists)).


%-----------------------------------------------------------------------------
% Dynamic Predicates
%
% FRAME(FrameName, Relationship, Super, Slots)
%	Slots = ListOfFacets
%-----------------------------------------------------------------------------
:- dynamic frame/4.


%-----------------------------------------------------------------------------
% ADD_FRAME(+FrameIdentifier, +Relationship, +Super, +Slots)
%-----------------------------------------------------------------------------
add_frame(FrameIdentifier, Relationship, Super, Slots) :-
	assert(frame(FrameIdentifier, Relationship, Super, Slots)).


%-----------------------------------------------------------------------------
% LIST_FRAMES
%-----------------------------------------------------------------------------
list_frames :-
	frame(Frame, _, Super, _),
	(var(Super); \+ frame(Super, _, _, _)),
	list_frames(Frame, 0),
	fail.

list_frames.


list_frames(Frame, Tab) :-
	dess_tab(Tab),
	dess_format('~p~n', [Frame]),
	NewTab is Tab + 4,
	frame(Sub, _, ThisFrame, _),
	nonvar(ThisFrame),
	ThisFrame = Frame,
	% Sub \== Frame,
	list_frames(Sub, NewTab),
	fail.

list_frames(_, _).


%-----------------------------------------------------------------------------
% SHOW_FRAMES
%-----------------------------------------------------------------------------
show_frames :- frame(Frame,_,_,_), show_frame(Frame), dess_format('~n',[]), fail.
show_frames.

show_frame(Frame) :-
	nonvar(Frame),
	frame(Frame, Rel, Super, Slots),
	dess_format('~p', [Frame]),
	(nonvar(Rel) ->
		dess_format(' ~p ~p~n', [Rel, Super])
	;
		dess_format('~n', [])
	),
	show_frame_slots(Slots),
	!.


show_frame_slots([]).

show_frame_slots([slot(SlotName, Facets)|_]) :-
	member(value(V, CF), Facets),
	dess_tab(4),
	dess_format('~p: ~p', [SlotName, V]),
	show_cf_if_not_one(CF),
	dess_format('~n', []),
	fail.

show_frame_slots([_|Slots]) :- show_frame_slots(Slots).


%-----------------------------------------------------------------------------
% UPDATE_FRAME(+Element, +CertaintyFactor)
%-----------------------------------------------------------------------------
update_frame(WME, CF) :-
	'DEBUG',
	dess_format('update_frame(~p,~p)~n', [WME, CF]),
	fail.

update_frame(fact(_), _).

update_frame(sub_condition(_), _).

update_frame(comparison(_,_,_), _).

update_frame(oav(O,A,V), CF) :- put_value(O,A,V,CF).

update_frame(instance(O, Super), _) :-
	retract(frame(O, _, _, Slots)),
	assert((frame(O, instance_of, Super, Slots))).

update_frame(subclass(O, Super), _) :-
	retract(frame(O, _, _, Slots)),
	assert((frame(O, subclass_of, Super, Slots))).


%-----------------------------------------------------------------------------
% GET_FRAME(+WME, -CF)
%-----------------------------------------------------------------------------
get_frame(oav(O,A,V), CF) :- nonvar(O), nonvar(A), get_value(O,A,V,CF,O).
get_frame(oav(O,A,V), CF) :- var(O), nonvar(V), get_object_with_value(O,A,V,CF).
get_frame(instance(A,B), 1.0) :- frame(A,instance_of,B,_), nonvar(B).
get_frame(subclass(A,B), 1.0) :- frame(A,subclass_of,B,_).


%-----------------------------------------------------------------------------
% GET_VALUE(+Object, +Attribute, -Value, -CertaintyFactor, +Frame)
%
% Look in frame 'Frame' for value or 'when_accessed' demon.
%
% Try to retrieve 'value' facet from object frame.
% Try to retrieve 'when_accessed' facet from object frame.
% Try to retrieve 'value' facet from superclass frame.
% Try to retrieve 'when_accessed' facet from superclass frame.
% Otherwise, value is 'UNKNOWN'.
%-----------------------------------------------------------------------------
get_value(_Object, Attribute, Value, CF, Frame) :-
	frame(Frame, _, _, Slots),
	nonvar(Slots),
	member(slot(Attribute, Facets), Slots),
	member(value(_, _), Facets),
	!,
	member(value(Value, CF), Facets).

get_value(Object, Attribute, Value, CF, Frame) :-
	frame(Frame, _, _, Slots),
	nonvar(Slots),
	member(slot(Attribute, Facets), Slots),
	member(when_accessed(Rule), Facets),
	Rule = rule(_, [if(_), then(Consequents)], _),
	member(wme(oav(Object, Attribute, Expression), CF), Consequents),
	bc_solve(Rule, CF),
	evaluate(Expression, Value),
	!.


get_value(Object, Attribute, Value, CF, Frame) :-
	frame(Frame, _, Super, _),
	nonvar(Super),
	frame(Super, _, _, _),
	!,
	get_value(Object, Attribute, Value, CF, Super).

get_value(_Object, _Attribute, 'UNKNOWN', 1.0, _).


%-----------------------------------------------------------------------------
% GET_OBJECT_WITH_VALUE(-Object, +Attribute, -Value, -CertaintyFactor)
%-----------------------------------------------------------------------------
get_object_with_value(Object, Attribute, Value, CF) :-
	frame(Object, instance_of, _, _),
	get_value(Object, Attribute, Value, CF, Object).


%-----------------------------------------------------------------------------
% PUT_VALUE(+Object, +Attribute, +Value, +CertaintyFactor)
%-----------------------------------------------------------------------------

put_value(Object, A, V, _) :-
	nonvar(V),
	V = unknown,
	frame(Object, Relationship, Super, Slots),
	delete(Slots, slot(A, Facets), OtherSlots),
	nonvar(Facets),
	member(value(_, _), Facets),
	!,
	delete(Facets, value(_, _), OtherFacets),
	retract(frame(Object, Relationship, Super, Slots)),
	assert(frame(Object, Relationship, Super,
		[slot(A, OtherFacets)|OtherSlots])).


% The given value is already present as a value for this slot.
% Combine the old and new certainty factors, and update the frame recording
% the amended certainty factor.

put_value(Object, A, V, NewCF) :-
	frame(Object, Relationship, Super, Slots),
	delete(Slots, slot(A, Facets), OtherSlots),
	nonvar(Facets),
	member(value(V, OldCF), Facets),
	!,
	combine_cf(OldCF, NewCF, CF),
	delete(Facets, value(V, OldCF), OtherFacets),
	retract(frame(Object, Relationship, Super, Slots)),
	assert(frame(Object, Relationship, Super,
		[slot(A, [value(V,CF)|OtherFacets])|OtherSlots])).


% This slot is single-valued, and has a different value at present.
% Modify the frame, replacing the old value with the new one.

put_value(Object, A, V, 1.0) :-
	frame(Object, Relationship, Super, Slots),
	delete(Slots, slot(A, Facets), OtherSlots),
	nonvar(Facets),
	member(value(_, _), Facets),
	get_cardinality(Object, A, single),
	!,
	delete(Facets, value(_, _), OtherFacets),
	retract(frame(Object, Relationship, Super, Slots)),
	assert(frame(Object, Relationship, Super,
		[slot(A, [value(V,1.0)|OtherFacets])|OtherSlots])).


% If the slot is single-valued, this clause will only be reached if the
% function does not yet have a value.

put_value(Object, A, V, CF) :-
	frame(Object, Relationship, Super, Slots),
	get_cardinality(Object, A, single),
	delete(Slots, slot(A, Facets), OtherSlots),
	nonvar(Facets),
	!,
	retract(frame(Object, Relationship, Super, Slots)),
	assert(frame(Object, Relationship, Super,
		[slot(A, [value(V,CF)|Facets])|OtherSlots])).


put_value(Object, A, V, CF) :-
	frame(Object, Relationship, Super, Slots),
	get_cardinality(Object, A, single),
	delete(Slots, slot(A, Facets), OtherSlots),
	var(Facets),
	!,
	retract(frame(Object, Relationship, Super, Slots)),
	assert(frame(Object, Relationship, Super,
		[slot(A, [value(V,CF)])|OtherSlots])).


% This is a multi-valued slot.

put_value(Object, A, V, CF) :-
	frame(Object, Relationship, Super, Slots),
	get_cardinality(Object, A, multi),
	delete(Slots, slot(A, Facets), OtherSlots),
	nonvar(Facets),
	!,
	retract(frame(Object, Relationship, Super, Slots)),
	assert(frame(Object, Relationship, Super,
		[slot(A, [value(V,CF)|Facets])|OtherSlots])).

put_value(Object, A, V, CF) :-
	frame(Object, Relationship, Super, Slots),
	get_cardinality(Object, A, multi),
	delete(Slots, slot(A, Facets), OtherSlots),
	var(Facets),
	!,
	retract(frame(Object, Relationship, Super, Slots)),
	assert(frame(Object, Relationship, Super,
		[slot(A, [value(V,CF)])|OtherSlots])).

put_value(Object, Attribute, Value, CF) :-
	assert(frame(Object, _, _, [slot(Attribute, [value(Value, CF)])])).


%-----------------------------------------------------------------------------
% GET_CARDINALITY(+Object, +Attribute, ?Cardinality)
%-----------------------------------------------------------------------------
get_cardinality(Object, Attribute, Cardinality) :-
	frame(Object, _, _, Slots),
	member(slot(Attribute, Facets), Slots),
	member(cardinality(StoredCardinality), Facets),
	!,
	Cardinality = StoredCardinality.

get_cardinality(Object, Attribute, Cardinality) :-
	frame(Object, _, Super, _),
	nonvar(Super),
	frame(Super, _, _, _),
	!,
	get_cardinality(Super, Attribute, Cardinality).

get_cardinality(_, _, single).


%-----------------------------------------------------------------------------
% PUT_CARDINALITY(+Object, +Attribute, +Cardinality)
%-----------------------------------------------------------------------------
put_cardinality(Object, Attribute, Cardinality) :-
	frame(Object, Relationship, Super, Slots),
	delete(Slots, slot(Attribute, Facets), OtherSlots),
	nonvar(Facets),
	!,
	retract(frame(Object, Relationship, Super, Slots)),
	assert(frame(Object, Relationship, Super,
		[slot(Attribute,
			[cardinality(Cardinality)|Facets])|OtherSlots])).

put_cardinality(Object, Attribute, Cardinality) :-
	frame(Object, Relationship, Super, Slots),
	delete(Slots, slot(Attribute, Facets), OtherSlots),
	var(Facets),
	!,
	retract(frame(Object, Relationship, Super, Slots)),
	assert(frame(Object, Relationship, Super,
		[slot(Attribute,
			[cardinality(Cardinality)])|OtherSlots])).

put_cardinality(Object, Attribute, Cardinality) :-
	assert(frame(Object, _, _,
		[slot(Attribute, [cardinality(Cardinality)])])).


%-----------------------------------------------------------------------------
% ADD_FRAME_TO_WM(+FrameName)
%-----------------------------------------------------------------------------
add_frame_to_wm(Frame) :-
	add_frame_super_to_wm(Frame),
	all_slotnames(Frame, BagOfSlotNames),
	remove_dups(BagOfSlotNames, SlotNames),
	member(Attribute, SlotNames),
	get_frame(oav(Frame, Attribute, Value), CF),
	Value \== 'UNKNOWN',
	add_wme(oav(Frame, Attribute, Value), 'Loaded from frame.', CF),
	fail.

add_frame_to_wm(_).

add_frame_super_to_wm(Frame) :-
	frame(Frame, Relationship, Super, _),
	(nonvar(Relationship) ->
		(Relationship = instance_of ->
			add_wme(instance(Frame, Super), 'Loaded from frame.',
				1.0)
		;
			add_wme(subclass(Frame, Super), 'Loaded from frame.',
				1.0)
		)
	;
		true
	).

all_slotnames(Frame, SlotNames) :-
	frame(Frame, _, Super, Slots),
	!,
	nonvar(Slots),
	findall(S, member(slot(S,_), Slots), LocalSlots),
	all_slotnames(Super, InheritedSlots),
	append(LocalSlots, InheritedSlots, SlotNames).

all_slotnames(_, []).


%-----------------------------------------------------------------------------
% DELETE_FRAME(+Frame)
%-----------------------------------------------------------------------------
delete_frame(Frame) :-
	nonvar(Frame),
	delete_dependent_frames(Frame),
	retract(frame(Frame, _, _, _)).


delete_dependent_frames(Frame) :-
	frame(DependentFrame, _, Super, _),
	nonvar(Super),
	Super = Frame,
	retract(frame(DependentFrame, _, _, _)),
	fail.

delete_dependent_frames(_).


%-----------------------------------------------------------------------------
% DELETE_SLOT_VALUE(+Object, +Attribute, +Value)
%-----------------------------------------------------------------------------
delete_slot_value(O,A,V) :-
	nonvar(O),
	nonvar(A),
	nonvar(V),
	frame(Object, Relationship, Super, Slots),
	delete(Slots, slot(A, Facets), OtherSlots),
	nonvar(Facets),
	member(value(V, _), Facets),
	!,
	delete(Facets, value(V, _), OtherFacets),
	retract(frame(Object, Relationship, Super, Slots)),
	assert(frame(Object, Relationship, Super,
		[slot(A, OtherFacets)|OtherSlots])).
