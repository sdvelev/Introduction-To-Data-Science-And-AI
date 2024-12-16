% remove_dups(List, Pruned)
% removes duplicated elements from List. The definition is obtained from
% the public libray "listro.pl".  Beware: if the List has non-ground
% elements, the result may surprise you.

remove_dups(A,B) :- list_to_set(A,B).


% file_exists(Filename)

file_exists(X) :- exists_file(X).
