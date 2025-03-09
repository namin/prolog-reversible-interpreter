% Simplified implementation of generalization from Figure 3 of the paper
% This focuses on the zip example and its generalization

:- op(250, fx, '*'). % * is prefixed to variables
:- op(250, fx, '/'). % / is prefixed to atoms
:- dynamic '$marker'/1.

% The zip program from Figure 3
zip_program([
    ([zip, [], *l, *l] :- []),
    ([zip, [*x | *l1], [*y | *l2], [*x, *y | *l3]] :- [[zip, *l1, *l2, *l3]])
]).

% The zip query from Figure 3
zip_query([[[zip, [/x,/y], [/z,/u], *ans]]]).

% The expected result
zip_result([[(*ans, [/x,/z,/y,/u])]]).

% Demonstrate the actual execution of zip
demonstrate_zip_execution :-
    zip_program(Program),
    zip_query(Query),
    zip_result(ExpectedResult),

    % Use the reversible interpreter to execute the program
    prolog(Program, Query, Result),

    writeln('Input program:'),
    maplist(writeln, Program),
    nl,
    writeln('Input query:'),
    writeln(Query),
    nl,
    writeln('Result:'),
    writeln(Result),
    nl,
    (Result = ExpectedResult ->
        writeln('Result matches expected output!')
    ;
        writeln('Result does not match expected output:'),
        writeln('Expected: '), writeln(ExpectedResult)
    ).

% This shows the generalization shown in Figure 3
% Where the specific predicate 'zip' is generalized to a variable PRED
% and specific constants are generalized to variables
demonstrate_zip_generalization :-
    % Original program from Figure 3
    Original = ([zip, [], *l, *l] :- []),

    % The generalized program - PRED replaces zip
    % This is directly from Figure 3 (bottom part)
    Generalized = ([PRED, [], *L, *L] :- []),

    writeln('Original clause:'),
    writeln(Original),
    nl,
    writeln('Generalized clause:'),
    writeln(Generalized),
    nl,

    % Second original clause
    Original2 = ([zip, [*x | *l1], [*y | *l2], [*x, *y | *l3]] :- [[zip, *l1, *l2, *l3]]),

    % Second generalized clause
    Generalized2 = ([PRED, [*X | *L1], [*Y | *L2], [*X, *Y | *L3]] :- [[PRED, *L1, *L2, *L3]]),

    writeln('Original clause 2:'),
    writeln(Original2),
    nl,
    writeln('Generalized clause 2:'),
    writeln(Generalized2),
    nl,

    % Show the original goal
    OrigGoal = prolog([Original, Original2],
                     [[[zip, [/x,/y], [/z,/u], *ans]]],
                     [[(*ans, [/x,/z,/y,/u])]]),

    % Show the generalized goal
    GenGoal = prolog([Generalized, Generalized2],
                    [[[PRED,[/E1,/E2],[/E3,/E4],*ANS]]],
                    [[(*ANS, [/E1,/E3,/E2,/E4])]]),

    writeln('Original goal:'),
    writeln(OrigGoal),
    nl,
    writeln('Generalized goal:'),
    writeln(GenGoal),
    nl,

    writeln('The key insight is that the specific predicate "zip" has been'),
    writeln('generalized to the variable PRED, and specific variable names'),
    writeln('like *l, *x, *y, etc. have been generalized to *L, *X, *Y.'),
    writeln('This allows the same pattern to be applied to other predicates.').

% Manual explanation of Figure 3
explain_figure3 :-
    writeln('EXPLANATION OF FIGURE 3 FROM THE PAPER:'),
    nl,
    writeln('Figure 3 shows the generalization of the zip program:'),
    nl,
    writeln('1. The original zip program:'),
    writeln('   zip([], L, L).'),
    writeln('   zip([X|L1], [Y|L2], [X,Y|L3]) :- zip(L1, L2, L3).'),
    nl,
    writeln('2. The generalization replaces:'),
    writeln('   - Specific predicate "zip" with a variable PRED'),
    writeln('   - Specific variables *l, *x, *y, etc. with *L, *X, *Y'),
    nl,
    writeln('3. The generalized program:'),
    writeln('   PRED([], L, L).'),
    writeln('   PRED([X|L1], [Y|L2], [X,Y|L3]) :- PRED(L1, L2, L3).'),
    nl,
    writeln('4. This generalization allows the pattern to be transferred to other predicates'),
    writeln('   such as "rzip" by instantiating PRED to "rzip".'),
    nl,
    writeln('5. Using the similar pattern, rzip would be defined as:'),
    writeln('   rzip([], L, L).'),
    writeln('   rzip([X|L1], [Y|L2], [Y,X|L3]) :- rzip(L1, L2, L3).'),
    nl,
    writeln('This is a simplified view of the generalization process.').

% The reversible interpreter (subset needed for demonstration)
prolog(_, [], []).
prolog(Clauses, [Q | Qs], [NewEnv | RestEnv]) :-
    goalseq(Q, [], NewEnv, Clauses),
    prolog(Clauses, Qs, RestEnv).

goalseq([], Env, Env, _Clauses).
goalseq([Goal | GRest], Env, NewEnv, Clauses) :-
    head(Goal, GG, Env, E),
    goal(GG, Clauses),
    goalseq(GRest, E, NewEnv, Clauses).

goal(Goal, Clauses) :-
    search(Clauses, (Head :- Body)),
    head(Head, Goal, [], NextEnv),
    goalseq(Body, NextEnv, _, Clauses).

search([Clause | _], Clause).
search([_ | Clauses], C) :- search(Clauses, C).

head([Pred | XA], [Pred | YA], OEnv, NEnv) :-
    head1(XA, YA, OEnv, NEnv).

head1([X | XRest], [Y | YRest], OEnv, NEnv) :-
    bind(X, Y, OEnv, Env),
    head1(XRest, YRest, Env, NEnv).
head1([], [], Env, Env).

bind(/X, /X, Env, Env).
bind([], [], Env, Env).
bind(*Var, Val, Env, NewEnv) :- fetch(*Var, Val, Env, NewEnv).
bind([X|XRest], [Val|ValRest], Env, NewEnv) :-
    bind(X, Val, Env, New1),
    bind(XRest, ValRest, New1, NewEnv).

fetch(Var, Val, Env, NewEnv) :- fetch1(Var, Val, Env, Env, NewEnv).

fetch1(Var, Val, [], Env, [(Var,Val)|Env]).
fetch1(Var, Val, [(Var, Val) | _Rest], Env, Env).
fetch1(Var1, Val, [(Var2, _) | EnvRest], Env, NewEnv) :-
    Var1 \== Var2,
    fetch1(Var1, Val, EnvRest, Env, NewEnv).

% Main entry point to show all demonstrations
show_generalization_demo :-
    writeln('===== DEMONSTRATION OF ZIP EXECUTION ====='),
    demonstrate_zip_execution,
    nl,
    writeln('===== DEMONSTRATION OF ZIP GENERALIZATION (FIGURE 3) ====='),
    demonstrate_zip_generalization,
    nl,
    writeln('===== EXPLANATION OF FIGURE 3 ====='),
    explain_figure3.
