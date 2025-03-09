% Reversible Prolog Interpreter for Inductive Program Synthesis
% Based directly on Numao & Shimura's paper

% Operator declarations - directly from paper, Appendix A
:- op(250, fx, '*'). % * is prefixed to variables
:- op(250, fx, '/'). % / is prefixed to atoms

% Dynamic declarations needed for SWI-Prolog but not shown in paper
:- dynamic '$marker'/1, etree/2, decomp_force/1.

% Initialize decomp_force (not specified in paper but needed)
:- retractall(decomp_force(_)), assertz(decomp_force(0)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% EXPLICITLY PROVIDED IN THE PAPER - Appendix A
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
% EXPLANATION-BASED LEARNING - Provided in the paper
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% EBG (Explanation-Based Generalization) - Provided on page 4
ebg(Goal, Head, Body) :-
    functor(Goal, F, N),
    functor(Head, F, N),
    ebg1(Goal, Head, Body, []).

ebg1(A, C, [C|G], G) :- operational(A), !, A.
ebg1(true, true, G, G) :- !.  % Special case for true not being dynamic
ebg1((A,B), (GenA,GenB), NG, OG) :-
    ebg1(A, GenA, NG, G),
    ebg1(B, GenB, G, OG).
ebg1(A, GenA, NG, OG) :-
    clause(GenA, GenB),
    copy((GenA :- GenB), (A :- B)),
    ebg1(B, GenB, NG, OG).
ebg1(true, _, G, G).

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
% EXECUTABLE EXPLANATION - PARTIALLY SPECIFIED IN THE PAPER
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% NOTE: This is where key implementation details are missing in the paper.
% The paper mentions "executable explanation" on page 7 but doesn't give
% a complete implementation.

% The paper specifies this on page 7:
etree(Id, Goal) :-
    composability(Goal, C),
    decomp_force(DECOMP_FORCE),
    DECOMP_FORCE >= C,
    clause(etree(SId, Goal), Body),
    nonvar(SId),
    Id \== SId,
    call(Body).

% Helper predicates for decomp_force (not specified in paper)
set_decomp_force(Value) :-
    retractall(decomp_force(_)),
    assertz(decomp_force(Value)).

inc_decomp_force :-
    decomp_force(D),
    NewD is D + 1,
    set_decomp_force(NewD).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% EXAMPLES FROM THE PAPER
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
    writeln(Head),
    writeln('Generalized Body:'),
    writeln(Body).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% MISSING PARTS - NOT FULLY SPECIFIED IN THE PAPER
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% MISSING: Complete implementation of executable explanation
% The paper describes on page 7 that executable explanation is
% "a set of prolog clauses directly representing the explanation"
% but doesn't provide complete code for how to generate these clauses.

% MISSING: Mechanisms for constructing the explanation structure
% The paper doesn't fully specify how to construct the explanation
% tree from program executions.

% MISSING: Specifics on the decomposition algorithm
% While the paper describes decomposition of explanations at various
% levels (clause-level, clause-structure-level, term-level), it doesn't
% provide complete implementation details.

% MISSING: Complete implementation for merging partial explanations
% The paper mentions transferring parts of explanations but doesn't
% provide complete details on this process.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% PROGRAM SYNTHESIS TESTS - BASED ON PAPER EXAMPLES
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Test for synthesizing merge3 from app3 - Based on Figure 5, page 8
% NOTE: THIS IS INCOMPLETE due to missing implementation details about
% how to construct executable explanations
test_merge3_synthesis :-
    % Reset
    retractall(etree(_,_)),
    retractall(decomp_force(_)),
    assertz(decomp_force(1)),

    % This is where we'd need to define the app3 explanation
    % The paper doesn't provide complete code for this part
    assertz(etree(1, prolog([([append,[],*x,*x]:-[]),
                           ([append,[*x|*l1],*l2,[*x|*l3]] :- [[append,*l1,*l2,*l3]]),
                           ([app3,*x,*y,*z,*a] :- [[append,*x,*y,*aa],
                                                   [append,*aa,*z,*a]])],
                          [[[app3,[/a],[/b],[/c],[/a,/b,/c]]]],
                          _Value))),

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
        writeln('Merge3 synthesis failed. Missing implementation details from paper.')
    ).

% Test for synthesizing rzip from zip - Based on Figure 8, page 10
% NOTE: THIS IS INCOMPLETE due to missing implementation details
test_rzip_synthesis :-
    % Reset
    retractall(etree(_,_)),
    retractall(decomp_force(_)),
    assertz(decomp_force(2)), % clause-structure-level

    % This is where we'd define the zip explanation
    assertz(etree(1, prolog([([zip, [], *l, *l] :- []),
                           ([zip, [*x | *l1], [*y | *l2], [*x, *y | *l3]]
                            :- [[zip, *l1, *l2, *l3]])],
                          [[[zip, [/x,/y], [/z,/u], *ans]]],
                          [[(*ans, [/x,/z,/y,/u])]]))),

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
        writeln('Rzip synthesis failed. Missing implementation details from paper.')
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

% Run the synthesis tests that use incomplete parts
run_synthesis_tests :-
    writeln('NOTE: These tests rely on implementation details not fully specified in the paper'),
    writeln('and are expected to fail without additional implementation.'),
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
    writeln('4. Missing Implementation Details:'),
    writeln('   - How to construct the executable explanation'),
    writeln('   - How to capture program execution structure'),
    writeln('   - How to merge partial explanations'),
    writeln('   - How to transfer between domains effectively').
