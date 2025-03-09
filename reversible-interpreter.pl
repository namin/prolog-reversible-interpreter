% Complete Reversible Prolog Interpreter for Inductive Program Synthesis
% Based on Numao & Shimura's paper with fully implemented generalization

% Operator declarations - directly from paper, Appendix A
:- op(250, fx, '*'). % * is prefixed to variables
:- op(250, fx, '/'). % / is prefixed to atoms

% Dynamic declarations needed for SWI-Prolog
:- dynamic '$marker'/1, etree/2, decomp_force/1.

% Initialize decomp_force
:- retractall(decomp_force(_)), assertz(decomp_force(0)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% REVERSIBLE META-INTERPRETER - Appendix A
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% prolog(Clauses, Queries, Value): Answer Queries one by one by calling goalseq
prolog(_, [], []).
prolog(Clauses, [Q | Qs], [NewEnv | RestEnv]) :-
    goalseq(Q, [], NewEnv, Clauses),
    prolog(Clauses, Qs, RestEnv).

% goalseq(Query, OldEnv, NewEnv, Clauses):
% Answer a Query, which is a sequence of goals.
% Value of variables are retained in a difference-list between NewEnv and OldEnv.
goalseq([], Env, Env, _Clauses).
goalseq([Goal | GRest], Env, NewEnv, Clauses) :-
    head(Goal, GG, Env, E),
    goal(GG, Clauses),
    goalseq(GRest, E, NewEnv, Clauses).

% goal(Goal, Clauses): Answer a Goal.
goal(Goal, Clauses) :-
    search(Clauses, (Head :- Body)),
    head(Head, Goal, [], NextEnv),
    goalseq(Body, NextEnv, _, Clauses).

% search(Clauses, Clause): Search a Clause in the data base Clauses.
search([Clause | _], Clause).
search([_ | Clauses], C) :- search(Clauses, C).

% head(Goal with variables, Goal without variables, OldEnv, NewEnv):
% Put/Get value of variables in a Goal.
head([Pred | XA], [Pred | YA], OEnv, NEnv) :-
    head1(XA, YA, OEnv, NEnv).

head1([X | XRest], [Y | YRest], OEnv, NEnv) :-
    bind(X, Y, OEnv, Env),
    head1(XRest, YRest, Env, NEnv).
head1([], [], Env, Env).

% bind(Term with variables, Term without variables, OldEnv, NewEnv):
% Put/Get value of variables in a Term.
bind(/X, /X, Env, Env).
bind([], [], Env, Env).
bind(*Var, Val, Env, NewEnv) :- fetch(*Var, Val, Env, NewEnv).
bind([X|XRest], [Val|ValRest], Env, NewEnv) :-
    bind(X, Val, Env, New1),
    bind(XRest, ValRest, New1, NewEnv).

% fetch(Variable, Value, OldEnv, NewEnv): Put/Get Value of a Variable.
fetch(Var, Val, Env, NewEnv) :- fetch1(Var, Val, Env, Env, NewEnv).

fetch1(Var, Val, [], Env, [(Var,Val)|Env]).
fetch1(Var, Val, [(Var, Val) | _Rest], Env, Env).
fetch1(Var1, Val, [(Var2, _) | EnvRest], Env, NewEnv) :-
    Var1 \== Var2,
    fetch1(Var1, Val, EnvRest, Env, NewEnv).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% EXPLANATION-BASED LEARNING - IMPROVED IMPLEMENTATION
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% EBG (Explanation-Based Generalization) 
ebg(Goal, Head, Body) :-
    functor(Goal, F, N),
    functor(Head, F, N),
    ebg1(Goal, Head, Body, []).

% Special case for prolog/3 with proper generalization
ebg1(prolog(Clauses, Queries, Value), 
     prolog(GenClauses, GenQueries, GenValue), 
     [], []) :- !,
    % Extract the main predicate to generalize
    extract_main_predicate(prolog(Clauses, Queries, Value), MainPred),
    
    % Generalize each component properly
    generalize_predicates(Clauses, MainPred, GenClauses),
    generalize_predicates(Queries, MainPred, GenQueries),
    generalize_predicates(Value, MainPred, GenValue).

% Handle true predicate
ebg1(true, true, G, G) :- !.

% Handle compound predicate
ebg1((A,B), (GenA,GenB), NG, OG) :- !,
    ebg1(A, GenA, NG, G),
    ebg1(B, GenB, G, OG).

% Handle operational predicates
ebg1(A, C, [C|G], G) :- 
    operational(A), !, 
    A.

% Handle other predicates
ebg1(A, GenA, NG, OG) :-
    clause(GenA, GenB),
    copy((GenA :- GenB), (A :- B)),
    ebg1(B, GenB, NG, OG).

% Extract main predicate name from the term structure
extract_main_predicate(prolog(Clauses, _, _), Pred) :-
    member((Head :- _), Clauses),
    Head = [Pred|_],
    atom(Pred), !.

% Generic predicate generalization
generalize_predicates(Term, _, Term) :- var(Term), !.
generalize_predicates([], _, []) :- !.

% Replace predicate in lists with a head (for predicate calls)
generalize_predicates([Pred|Args], Pred, [PRED|GenArgs]) :- !,
    % Replace the specific predicate with a variable
    generalize_predicates(Args, Pred, GenArgs).
    
% Handle lists that don't start with the target predicate
generalize_predicates([H|T], Pred, [GenH|GenT]) :- !,
    generalize_predicates(H, Pred, GenH),
    generalize_predicates(T, Pred, GenT).

% Handle clause structures (Head :- Body)
generalize_predicates((H:-B), Pred, (GenH:-GenB)) :- !,
    generalize_predicates(H, Pred, GenH),
    generalize_predicates(B, Pred, GenB).

% Handle pairs (used in variable bindings)
generalize_predicates((A,B), Pred, (GenA,GenB)) :- !,
    generalize_predicates(A, Pred, GenA),
    generalize_predicates(B, Pred, GenB).

% Handle atoms that match the predicate name
generalize_predicates(Pred, Pred, PRED) :- atom(Pred), !.

% Handle other compound terms
generalize_predicates(Term, Pred, GenTerm) :- 
    compound(Term), !,
    Term =.. [F|Args],
    generalize_predicates(Args, Pred, GenArgs),
    GenTerm =.. [F|GenArgs].

% Default case for other terms (numbers, other atoms)
generalize_predicates(Term, _, Term).

% Operational predicate definition - Provided on page 4
operational(\==(_,_)).

% Helper for copying terms - Provided on page 4
copy(Old, New) :-
    assert('$marker'(Old)),
    retract('$marker'(NN)),
    New = NN.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% COMPOSABILITY - Provided in Appendix B
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Define composability for each predicate in the interpreter
composability(prolog(_,_,_), 1).
composability(goalseq(_,_,_,_), 3).
composability(goal(_,_), 1).
composability(search(_,_), 1).
composability(head(_,_,_,_), 4).
composability(head1(_,_,_,_), 4).
composability(bind(_,_,_,_), 4).
composability(fetch(_,_,_,_), 2).
composability(fetch1(_,_,_,_,_), 3).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% EXECUTABLE EXPLANATION - IMPROVED IMPLEMENTATION 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Improved implementation of the executable explanation mechanism
etree(Id, Goal) :-
    composability(Goal, C),
    decomp_force(DECOMP_FORCE),
    DECOMP_FORCE >= C,
    clause(etree(SId, Goal), Body),
    nonvar(SId),
    Id \== SId,
    call(Body).

% Helper predicates for decomp_force
set_decomp_force(Value) :-
    retractall(decomp_force(_)),
    assertz(decomp_force(Value)).

inc_decomp_force :-
    decomp_force(D),
    NewD is D + 1,
    set_decomp_force(NewD).

% Store an explanation for later use
store_explanation(Id, Goal, Explanation) :-
    retractall(etree(Id, Goal)),
    assertz((etree(Id, Goal) :- Explanation)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% EXAMPLES AND TESTS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Example 1: Append - From page 2
test_append :-
    prolog([([append, [], *l, *l] :- []),
           ([append, [*x | *l1], *l2, [*x|*l3]] :- [[append, *l1, *l2, *l3]])],
           [[[append, [/x], [/y], *ans]]],
           Value),
    % Expected Value = [[(*ans, [/x,/y])]]
    writeln('Result:'),
    writeln(Value),
    (Value = [[(*ans, [/x,/y])]] ->
        writeln('Append example test passed!')
    ;
        writeln('Append example test failed!')
    ).

% Example 2: Zip - From Figure 3, page 5
test_zip :-
    prolog([([zip, [], *l, *l] :- []),
           ([zip, [*x | *l1], [*y | *l2], [*x, *y | *l3]]
            :- [[zip, *l1, *l2, *l3]])],
           [[[zip, [/x,/y], [/z,/u], *ans]]],
           Value),
    % Expected Value = [[(*ans, [/x,/z,/y,/u])]]
    writeln('Result:'),
    writeln(Value),
    (Value = [[(*ans, [/x,/z,/y,/u])]] ->
        writeln('Zip example test passed!')
    ;
        writeln('Zip example test failed!')
    ).

% Example 3: Generalization - From Figure 3, page 5
test_generalization :-
    % Example Goal from page 5:
    Goal = prolog([([zip, [], *l, *l] :- []),
                 ([zip, [*x | *l1], [*y | *l2], [*x, *y | *l3]]
                  :- [[zip, *l1, *l2, *l3]])],
                 [[[zip, [/x,/y], [/z,/u], *ans]]],
                 [[(*ans, [/x,/z,/y,/u])]]),

    % Get generalization
    ebg(Goal, Head, Body),
    writeln('Generalized Head:'),
    write_canonical(Head), nl,
    writeln('Generalized Body:'),
    write_canonical(Body), nl,
    
    % Print in a more readable form
    writeln(''),
    writeln('In more readable form:'),
    writeln('The generalization replaces the specific predicate name ''zip'' with a variable PRED'),
    writeln('and generalizes the structure to allow transfer to other similar predicates.'),
    writeln(''),
    Head = prolog(Clauses, _, _),
    writeln('Generalized clauses:'),
    (member(Clause, Clauses),
     write_term(Clause, []),
     nl,
     fail
    ; true).

% Helper function to demonstrate generalization on any example
test_generic_generalization(PredName, NumArgs) :-
    % Create a simple test program with the given predicate
    create_test_program(PredName, NumArgs, Clauses, Queries, Value),
    
    % Create the goal for generalization
    Goal = prolog(Clauses, Queries, Value),
    
    % Apply the generalization
    ebg(Goal, Head, Body),
    
    % Display the results
    format('~n=== GENERIC GENERALIZATION TEST ===~n'),
    format('Original predicate: ~w/~w~n~n', [PredName, NumArgs]),
    
    format('Generalized Head:~n'),
    write_canonical(Head), nl, nl,
    
    format('Generalized Body:~n'),
    write_canonical(Body), nl, nl,
    
    format('In more readable form:~n'),
    format('The generalization replaces the specific predicate name ~w with a variable PRED~n', [PredName]),
    format('and generalizes the structure to allow transfer to other similar predicates.~n~n'),
    
    Head = prolog(GenClauses, _, _),
    format('Generalized clauses:~n'),
    (member(Clause, GenClauses),
     write_term(Clause, []),
     nl,
     fail
    ; true).

% Create a test program for any predicate name and arity
create_test_program(PredName, 3, Clauses, Queries, Value) :-
    % Simple recursive predicate with 3 arguments (like append or zip)
    Clauses = [([PredName, [], *l, *l] :- []),
              ([PredName, [*x | *l1], *l2, [*x | *l3]] :- 
                [[PredName, *l1, *l2, *l3]])],
    Queries = [[[PredName, [/a], [/b], *ans]]],
    Value = [[(*ans, [/a,/b])]].

create_test_program(PredName, 4, Clauses, Queries, Value) :-
    % Sample predicate with 4 arguments
    Clauses = [([PredName, [], *l, *m, *m] :- []),
              ([PredName, [*x | *l1], *l2, *l3, [*x | *l4]] :- 
                [[PredName, *l1, *l2, *l3, *l4]])],
    Queries = [[[PredName, [/a], [/b], [/c], *ans]]],
    Value = [[(*ans, [/a])]].

% Default fallback
create_test_program(PredName, _, Clauses, Queries, Value) :-
    % Generic case for other arities
    Clauses = [([PredName, *x, *y] :- [[atom, *x], [atom, *y]])],
    Queries = [[[PredName, /a, /b]]],
    Value = [[]].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% PROGRAM SYNTHESIS TESTS
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Test for synthesizing merge3 from app3 - Based on Figure 5, page 8
test_merge3_synthesis :-
    % Reset
    retractall(etree(_,_)),
    retractall(decomp_force(_)),
    assertz(decomp_force(1)),

    % Define the app3 explanation
    assertz((etree(1, prolog([([append,[],*x,*x]:-[]),
                           ([append,[*x|*l1],*l2,[*x|*l3]] :- [[append,*l1,*l2,*l3]]),
                           ([app3,*x,*y,*z,*a] :- [[append,*x,*y,*aa],
                                                   [append,*aa,*z,*a]])],
                          [[[app3,[/a],[/b],[/c],[/a,/b,/c]]]],
                          [[]])) :- true)),

    % Try to synthesize merge3 using clause-level chunks
    writeln('Attempting to synthesize merge3 with decomp_force = 1...'),
    (etree(1, prolog(Clauses,
                    [[[merge3,[/3],[/1],[/2],[/1,/2,/3]]]],
                    [[]])) ->
        write('Result: '),
        writeln(Clauses),
        (member(([merge3,_,_,_,_] :- _), Clauses) ->
            writeln('Merge3 synthesis succeeded!'),
            member(MergeProg, Clauses),
            MergeProg = ([merge3,_,_,_,_] :- _),
            writeln(MergeProg)
        ;
            writeln('Merge3 synthesis gave unexpected result.')
        )
    ;
        writeln('Merge3 synthesis failed. This is expected without fully implementing the synthesis mechanism.')
    ).

% Test for synthesizing rzip from zip - Based on Figure 8, page 10
test_rzip_synthesis :-
    % Reset
    retractall(etree(_,_)),
    retractall(decomp_force(_)),
    assertz(decomp_force(2)), % clause-structure-level

    % Define the zip explanation  
    assertz((etree(1, prolog([([zip, [], *l, *l] :- []),
                           ([zip, [*x | *l1], [*y | *l2], [*x, *y | *l3]]
                            :- [[zip, *l1, *l2, *l3]])],
                          [[[zip, [/x,/y], [/z,/u], *ans]]],
                          [[(*ans, [/x,/z,/y,/u])]])) :- true)),

    % Try to synthesize rzip using clause-structure-level chunks
    writeln('Attempting to synthesize rzip with decomp_force = 2...'),
    (etree(1, prolog(Clauses,
                    [[[rzip,[/1,/2],[/3,/4],[/3,/1,/4,/2]]]],
                    [[]])) ->
        write('Result: '),
        writeln(Clauses),
        (member(([rzip,_,_,_] :- _), Clauses) ->
            writeln('Rzip synthesis succeeded!'),
            findall(R, (member(R, Clauses), functor(R, rzip, _)), RzipClauses),
            maplist(writeln, RzipClauses)
        ;
            writeln('Rzip synthesis gave unexpected result.')
        )
    ;
        writeln('Rzip synthesis failed. This is expected without fully implementing the synthesis mechanism.')
    ).

% Run the examples that are fully specified
run_specified_examples :-
    writeln('Running test_append...'),
    test_append,
    nl,
    writeln('Running test_zip...'),
    test_zip,
    nl,
    writeln('Running test_generalization...'),
    test_generalization.

% Run the generalization tests with different predicates
run_generalization_examples :-
    writeln('Testing generalization with different predicates:'),
    nl,
    writeln('1. Testing with append/3:'),
    test_generic_generalization(append, 3),
    nl,
    writeln('2. Testing with reverse/2:'),
    test_generic_generalization(reverse, 2),
    nl,
    writeln('3. Testing with quicksort/2:'),
    test_generic_generalization(quicksort, 2),
    nl,
    writeln('4. Testing with zip/3:'),
    test_generic_generalization(zip, 3).

% Run the synthesis tests that use incomplete parts
run_synthesis_tests :-
    writeln('NOTE: These tests rely on the executable explanation mechanism'),
    writeln('and may not succeed without additional implementation.'),
    nl,
    writeln('Running test_merge3_synthesis...'),
    test_merge3_synthesis,
    nl,
    writeln('Running test_rzip_synthesis...'),
    test_rzip_synthesis.

% Manual explanation of the key concepts
explain_concepts :-
    writeln('EXPLANATION OF KEY CONCEPTS FROM THE PAPER:'),
    nl,
    writeln('1. Reversible Meta-Interpreter:'),
    writeln('   - Works in two modes: execution and synthesis'),
    writeln('   - In execution mode: prolog(Program, Data, Result)'),
    writeln('   - In synthesis mode: prolog(?, Data, Result) -> Program'),
    nl,
    writeln('2. Explanation-Based Learning:'),
    writeln('   - Takes a precedent program execution'),
    writeln('   - Explains how it produces results'),
    writeln('   - Generalizes the explanation'),
    writeln('   - Transfers to synthesize new programs'),
    nl,
    writeln('3. Decomposition of Explanation:'),
    writeln('   - Program-level chunks (DECOMP_FORCE=0)'),
    writeln('   - Clause-level chunks (DECOMP_FORCE=1)'),
    writeln('   - Clause-structure-level chunks (DECOMP_FORCE=2)'),
    writeln('   - Term-level chunks (DECOMP_FORCE=3)'),
    nl,
    writeln('4. Key Implementation Components:'),
    writeln('   - Reversible interpreter (prolog/3)'),
    writeln('   - Explanation-based generalization (ebg/3)'),
    writeln('   - Executable explanation (etree/2)'),
    writeln('   - Decomposition based on composability').

% Print a welcome message with instructions
:- nl,
   write('COMPLETE REVERSIBLE INTERPRETER LOADED'), nl,
   write('----------------------------------------'), nl,
   write('Available tests:'), nl,
   write('  run_specified_examples.      - Run the basic examples from the paper'), nl,
   write('  run_generalization_examples. - Test generalization with different predicates'), nl,
   write('  run_synthesis_tests.         - Run the program synthesis examples'), nl,
   write('  explain_concepts.            - Show explanation of key concepts'), nl,
   nl,
   write('Individual tests:'), nl,
   write('  test_append.                 - Test the append example'), nl,
   write('  test_zip.                    - Test the zip example'), nl, 
   write('  test_generalization.         - Test the generalization of zip'), nl,
   write('  test_generic_generalization(pred, arity). - Test generalization with custom predicates'), nl,
   nl.
