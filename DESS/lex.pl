%-----------------------------------------------------------------------------
% Copyright (C) : University of Aberdeen, Graham J.L. Kemp.
%
% Demonstration Expert System Shell (DESS)
%-----------------------------------------------------------------------------





%-----------------------------------------------------------------------------
% READ_COMMAND(-List)
%
% Taken from P/FDM source file 'daplex_lex.pl'.
%-----------------------------------------------------------------------------
read_command(Res) :-
	(noecho ->
		Echo = noecho
	;
		Echo = echo
	),
	get0(X),
	read_command(X, Res, Echo).


read_command(X, [Unit|List], Echo) :-
	X \== 59,				% Next char not semi-colon.
	skip_spaces(X, Y, Echo),
	Y \== 59,				% White space not followed by
	!,					% a semi-colon.
	read_unit(Y, Unit, Z, Echo),
	read_command(Z, List, Echo).

read_command(_, [], _).


%-----------------------------------------------------------------------------
% SKIP_SPACES(+InChar, -OutChar, +Echo)
%
% Called from read_command/3.
%-----------------------------------------------------------------------------
skip_spaces(X, Z, Echo) :-
	skip_space(X, Y, Echo),
	!,
	skip_spaces(Y, Z, Echo).

skip_spaces(X, X, _).


%-----------------------------------------------------------------------------
% SKIP_SPACE(+InChar, -OutChar, +Echo)
%
% Called from skip_spaces/3.
%
% If the next character in the current input stream is a space, tab or newline
% character, then skip over it.
% If the next character is '%', then skip the rest of the current line.
%-----------------------------------------------------------------------------
skip_space(X, Y, Echo) :-
	is_white(X),
	!,
	(Echo=echo -> daplex_lex_put_char(X); true),
	get0(Y).

skip_space(X, Y, Echo) :-
	is_newline(X),
	!,
	(Echo=echo -> daplex_lex_put_char(newline); true),
	get0(Y).

skip_space(37, Y, _) :-				% Percent sign, signalling a
	!,					% Daplex comment.
	skip(10),				% Skip all input to newline.
	get0(Y).


%-----------------------------------------------------------------------------
% READ_UNIT(+InChar, -Unit, -OutChar, +Echo)
%
% Called from read_command/3.
%
% X is the next "non-space" character in the current input stream.
% If X is a semi-colon, or end of file character, indicating that the end of
% the command has been reached, then this routine will fail.
% Otherwise, this routine will succeed with next word, number, string or
% symbol in the command being the value of Unit.
%
% If the unit read is a quoted string, then the value of Unit will be a term
% of the form string(String), i.e. if the file contains "abc", then the value
% of Unit will be string('abc').
% Behind this is our decision that all strings in Daplex commands ought to be
% explicit by being in quotes (the user is will be free to use any kind of
% quote).  This will avoid possible ambiguities between strings and the names
% of variables, and will allow more helpful error-checking to be done by the
% Daplex parser.
%-----------------------------------------------------------------------------
read_unit(X, _, -1, _) :-
	is_endfile(X),
	!,
	fail.

read_unit(59, _, 59, Echo) :-			% Semi-colon, signalling the
	!,					% end of a Daplex command.
	(Echo=echo -> daplex_lex_put_char(59); true),
	fail.

read_unit(X, Unit, Y, Echo) :-
	is_alpha(X),
	!,
	read_word(X, CharacterList, Y, Echo),
	name(Unit, CharacterList).

read_unit(X, Unit, Y, Echo) :-
	is_digit(X),
	!,
	read_number(X, CharacterList, Y, Echo),
	name(Unit, CharacterList).

read_unit(X, string(Unit), Y, Echo) :-
	is_quote(X),
	!,
	(Echo=echo -> daplex_lex_put_char(X); true),
	get0(Character),
	read_string(X, Character, CharacterList, Z, Echo),
	(Echo=echo -> daplex_lex_put_char(Z); true),
	get0(Y),
	atom_chars(Unit, CharacterList).

read_unit(X, Symbol, Y, Echo) :-
	% The next character is a symbol.
	% Operators containing more than one symbol (e.g. '>=') will not be
	% constructed here (i.e. two symbols, '>' and '=', will be returned).
	% At present, the task of combining these symbols is done by the parser.
	(Echo=echo -> daplex_lex_put_char(X); true),
	get0(Y),
	name(Symbol, [X]).


%-----------------------------------------------------------------------------
% READ_WORD(+InChar, -List, -OutChar, +Echo)
%
% Called from read_unit/4.
%
% On the initial call, Character is known to be a letter.  Subsequent letters,
% digits and underscore characters are read to complete the word.
%-----------------------------------------------------------------------------
read_word(X, [X|List], Y, Echo) :-
	is_csym(X),
	!,
	(Echo=echo -> daplex_lex_put_char(X); true),
	get0(X1),
	read_word(X1, List, Y, Echo).

read_word(X, [], X, _).


%-----------------------------------------------------------------------------
% READ_NUMBER(+InChar, -List, -OutChar, +Echo)
%
% Called from read_unit/4.
%-----------------------------------------------------------------------------
read_number(X, [X|List], Y, Echo) :-
	(	is_digit(X)
	;
		X = 46				% Decimal point
	),
	!,
	(Echo=echo -> daplex_lex_put_char(X); true),
	get0(X1),
	read_number(X1, List, Y, Echo).

read_number(X, [], X, _).


%-----------------------------------------------------------------------------
% READ_STRING(+Quote +InChar, -List, -OutChar, +Echo)
%
% Called from read_unit/4.
%
% A quote symbol, Quote, has just  been read.
% Read a string of characters up to the next matching quote symbol.
%-----------------------------------------------------------------------------
read_string(Quote, Quote, [], Quote, _).

read_string(Quote, X, [X|List], Y, Echo) :-
	!,
	(Echo=echo -> daplex_lex_put_char(X); true),
	get0(X1),
	read_string(Quote, X1, List, Y, Echo).


%-----------------------------------------------------------------------------
% DAPLEX_LEX_PUT_CHAR(+Character)
%
% Called from skip_space/3.
% Called from read_unit/4.
% Called from read_word/4.
% Called from read_number/4.
% Called from read_string/5.
%
% Given an ASCII code number, echo the corresponding character to the current
% output stream.
%
% 15/07/2002 GJLK:
%	Formerly put_char/1, but renamed to avoid a name clash when put_char/1
%	was introduced as a built-in predicate in SICStus Prolog.
%-----------------------------------------------------------------------------
daplex_lex_put_char(newline) :- nl, !.
daplex_lex_put_char(X) :- put(X).





%----------------------------------------------------------------------------
% pfdm_ctypes.pl (used by daplex_lex.pl, parser_support.pl):
%
%   * is_alpha/1	: obtained from the public domain library "ctypes.pl".
%   # is_csym/1   	: public domain libraries do not have this, but we can
%		      	  define it based on predicates in public libraries
%		      	  (i.e. is_alpha/1, is_digit/1).
%			   In Quintus, is_csysm/1:
%			  %   is_csym(?Char)
%			  %   is true when Char is the code of a character
%			  %   which could occur in the body of an identifier
%			  %   (it is a letter, digit, or underscore).
%
%		          "is_csym/1" is called only once in "daplex_lex.pl"
%			  and "parser_support.pl".
%   * is_digit/1	: obtained from the public library "ctypes.pl".
%   ? is_endfile	: In Quitus, it is "is_endfile(-1)", while in public
%                         domain library "ctypes.pl", it's "is_endfile(26)".
%			  (It is 26 in Dec-10 and C Prolog.) We use "-1".
%   # is_lower/1	: our definition is more efficient than that given
%			  in the public library "ctypes.pl".
%   ? is_newline/1	: We define "is_newline(10)" as in Quitus, not as in
%		    	  the public library (ctypes.pl) "is_newline(31)".
%		    	  This predicate is OS-dependent. This is 10 on UNIX,
%			  13 in systems where CR is the line terminator, and
%			  is 31 in systems where CR+LF is the terminator.
%   = is_quote/1  	: obtained from the public library "ctypes.pl".
%
% Predicates marked by a "*" are defined in Prolog public domain library
% "ctypes.pl".  However, their defintions are different from the definitions
% in the "commercial" Quintus Prolog.  We do not know yet whether they will
% behave the same as the predicates defined in Quintus.
%
% Predicates marked by a "#" are defined in Quintus Prolog, but not in public
% libraries.  We have defined them based on predicates in public libraries.
%
% Predicates marked by a "=" have the same definition in the public domain
% library as in Quintus Prolog libraries.
%
% Predicates marked by a "?" have chosen to use Quintus' definition, rather
% than using definitions from the public libraries.  Scott's versio of SISCTUS
% P/FDM calls Quintus libraries directly, and it works well.
%
%----------------------------------------------------------------------------
is_alpha(C) :-
        is_lower(C).

is_alpha(C) :-
        is_upper(C).

is_alpha(0'_).         % underscore "_".


is_digit(C) :-
	C >= "0",
	C =< "9".

% We define is_csym/1 based on the public predicates is_alpha/1 & is_digit/1.
% Note that is_alpha/1 takes account the "_" (underscore).

is_csym(C):-
     ( is_alpha(C)
     ;
       is_digit(C)
     ).

is_endfile(-1).    % It's "26" in Dec-10 and C Prolog (also in public domain
		   % library).


is_lower(C) :-
	C >= "a",
	C =< "z".

is_upper(C) :-
	C >= "A",
	C =< "Z".


is_newline(10).     % Same as in Quintus. The definition in public library
		    % "ctype.pl" is is_newline(31).  It's OS-dependent.

is_quote(0'').
is_quote(0'").
is_quote(0'`).

% We define "is_white/1" as below (NB: the definition of "is_space/1" is
% obtained from the public library "ctypes.pl"):

is_white(X):- is_space(X).

is_space(32).                   % space
is_space( 9).                   % tab
