-module(redex).

% API exports
-export([reduce/1]).

% test exports
-export([run/0, sample/0]).

-type set(X) :: #{X => 1}.
-type set_list(SetId, Element) :: [{SetId, set(Element)}].
-type element_sets(Element, SetId) :: #{Element => set(SetId)}.
-type set_elements(SetId, Element) :: #{SetId => set(Element)}.

-type plan_entry(SetId, Element) :: {
    Sets :: set(SetId),
    From :: set(Element),
    To :: set(Element)
}.
-type plan(SetId, Element) :: [plan_entry(SetId, Element)].

verbose(_Fun) -> ok.

-spec reduce(set_list(SetId, Element)) -> set_list(SetId, Element).
reduce(SetList) ->
    % step one - find groups an element is a member of
    % ElSetMap :: element_sets(_Elem, _SetId)
    ElSetMap = lists:foldl(
        fun({SetId, M}, Acc) ->
            maps:fold(fun(K, _V, A) -> update_mmap(K, SetId, A, 1) end, Acc, M)
        end,
        #{},
        SetList
    ),

    verbose(fun() ->
        print("\nelement-sets:\n", maps:to_list(ElSetMap))
    end),

    PlanList = steps(ElSetMap, []),

    % show interim steps
    verbose(fun() ->
        lists:foldr(
            fun(Plan, Plans) ->
                Plans_ = Plan ++ Plans,
                print("\nsets:\n", subst(SetList, Plans_)),
                Plans_
            end,
            [],
            PlanList
        )
    end),

    subst(SetList, lists:concat(PlanList)).

-spec steps(element_sets(Element, SetId), [plan(SetId, Element)]) -> [plan(SetId, Element)].
steps(ElSetMap, Plans) ->
    case make_plan(ElSetMap) of
        [] ->
            Plans;
        Plan ->
            verbose(fun() -> print_plan_steps(Plan) end),
            steps(subst_(ElSetMap, Plan), [Plan | Plans])
    end.

-spec make_plan(element_sets(Element, SetId)) -> plan(SetId, Element).
make_plan(ElSetMap) ->
    % find pairs common for more than one set
    % L1 :: [{PairSets::set(SetId), Match::boolen(), Vars::set(Element)}]
    L1 = fold_pairs(
        fun(K1, V1, K2, V2, Acc) ->
            if
                V1 =:= V2, map_size(V1) > 1 ->
                    [{V1, true, maps:from_keys([K1, K2], 1)} | Acc];
                true ->
                    case maps:intersect(V1, V2) of
                        PairSets when map_size(PairSets) > 1 ->
                            [{PairSets, false, maps:from_keys([K1, K2], 1)} | Acc];
                        _ ->
                            Acc
                    end
            end
        end,
        [],
        ElSetMap
    ),
    verbose(fun() -> print_("\nsets-to-common-pair list:\n", L1) end),

    % sort it, so the most frequent pairs go first,
    % for same set-fequency, higher order of substitution wins
    % L1 :: [{SetsM::set(SetId), MergeVars::boolen(), VarsM::set(Element)}]
    L2 = lists:sort(
        fun
            ({A, _, _}, {B, _, _}) when map_size(A) > map_size(B) -> true;
            ({A, _, _}, {B, _, _}) when map_size(A) < map_size(B) -> false;
            ({_, M, A}, {_, _, B}) ->
                S1 = deep_size(A),
                S2 = deep_size(B),
                if
                    S1 > S2 -> true;
                    S1 < S2 -> false;
                    M =:= true -> true;
                    true -> false
                end
        end,
        L1
    ),
    verbose(fun() -> print_("\nsame shit sorted:\n", L2) end),

    % build "substitution plan"
    % since we filter out vars already used in the same sets from
    % replacement candidates, the order of the output is not important here,
    % only order of input list of sets-pairs is important
    {_, L3} = lists:foldl(
        fun({SetsM, MergeVars, VarsM}, {UsedVarsMap, Acc}) ->
            % create set of used vars for the current context (set of set-ids)
            % SetsM :: set(SetId), MergeVars :: boolean(), VarsM :: set(Element)
            Used = maps:fold(
                fun(SetId, _, Acc1) ->
                    UsedVars = maps:get(SetId, UsedVarsMap, #{}),
                    maps:merge(Acc1, UsedVars)
                end,
                #{},
                SetsM
            ),

            % exclude used vars, do the job
            case maps:without(maps:keys(Used), VarsM) of
                % we good to go and substitute
                VarsM_ when map_size(VarsM_) > 1 ->
                    % #{SetId => VarsM :: set(Element)}
                    {update_used_vars(UsedVarsMap, VarsM_, SetsM), [
                        {SetsM, VarsM_, maybe_merge_vars(MergeVars, VarsM_)} | Acc
                    ]};
                _ ->
                    {UsedVarsMap, Acc}
            end
        end,
        {#{}, []},
        L2
    ),
    verbose(fun() -> print2("\nplan:\n", lists:reverse(L3)) end),
    L3.

-spec update_used_vars(set_elements(SetId, Element), set(Element), Element) ->
    set_elements(SetId, Element).
update_used_vars(UsedVarsMap, VarsM_, SetsM) ->
    maps:merge_with(
        fun(_SetId, U1, U2) -> maps:merge(U1, U2) end,
        UsedVarsMap,
        maps:map(fun(_SetId, _) -> VarsM_ end, SetsM)
    ).

maybe_merge_vars(true, M) ->
    [A, B] = maps:keys(M),
    merge_vars(A, B);
maybe_merge_vars(false, M) ->
    M.

merge_vars(M1, M2) when is_map(M1), is_map(M2) ->
    maps:merge(M1, M2);
merge_vars(M, V) when is_map(M) ->
    M#{V => 1};
merge_vars(V, M) when is_map(M) ->
    M#{V => 1};
merge_vars(V1, V2) ->
    maps:from_keys([V1, V2], 1).

% apply to element-sets map...
-spec subst_(element_sets(Element, SetId), plan(SetId, Element)) ->
    element_sets(Element, SetId).
subst_(ElSetMap, Plan) ->
    ElSetMap_ = lists:foldr(
        fun({Sets, From, To}, Acc) ->
            % add "resplacement"
            Acc_ = Acc#{To => Sets},

            % remove pattern Sets from variable sets for each Var in From vars
            maps:filtermap(
                fun(Var, Sets_) ->
                    case maps:is_key(Var, From) of
                        true ->
                            case maps:without(maps:keys(Sets), Sets_) of
                                Sets__ when map_size(Sets__) > 0 ->
                                    {true, Sets__};
                                _ ->
                                    false
                            end;
                        false ->
                            true
                    end
                end,
                Acc_
            )
        end,
        ElSetMap,
        Plan
    ),
    verbose(fun() ->
        print("\nold element-sets map:\n", lists:sort(maps:to_list(ElSetMap))),
        print("\nnew element-sets map:\n", lists:sort(maps:to_list(ElSetMap_)))
    end),
    ElSetMap_.

% substitute vars in LM per plan
-spec subst(set_list(SetId, Element), plan(SetId, Element)) -> set_list(SetId, Element).
subst(LM, Plan) ->
    lists:map(
        fun({SetId, M}) ->
            M_ = lists:foldr(
                fun({Sets, From, To}, Acc) ->
                    case maps:is_key(SetId, Sets) of
                        true ->
                            maps:put(To, 1, maps:without(maps:keys(From), Acc));
                        false ->
                            Acc
                    end
                end,
                M,
                Plan
            ),
            {SetId, M_}
        end,
        LM
    ).

-spec print_plan_steps(plan(_SetId, _Element)) -> ok.
print_plan_steps(Plan) ->
    io:format("~napply to element-sets maps...~n"),
    lists:foreach(
        fun({Sets, From, To}) ->
            io:put_chars("plan step: "),
            print_set(Sets),
            io:put_chars(" : "),
            print_set(From),
            io:put_chars(" -> "),
            print_set(To),
            io:put_chars("\n")
        end,
        Plan
    ).

print(Head, LM) ->
    io:put_chars(Head),
    print(LM).

print2(Head, LM) ->
    io:put_chars(Head),
    print2(LM).

print_(Head, LM) ->
    io:put_chars(Head),
    print_(LM).

print(LM) ->
    lists:foreach(
        fun({Key, Val}) ->
            print_set(Key),
            io:format(": "),
            print_set(Val),
            io:format("~n")
        end,
        LM
    ).

print2(LM) ->
    lists:foreach(
        fun({Key, From, To}) ->
            print_set(Key),
            io:format(": "),
            print_set(From),
            io:format(" -> "),
            print_set(To),
            io:format("~n")
        end,
        LM
    ).

print_(LM) ->
    lists:foreach(
        fun({Key, Merge, Val}) ->
            print_set(Key),
            io:format(": "),
            print_set(Val),
            if
                Merge ->
                    io:put_chars(" (merge)");
                true ->
                    ok
            end,
            io:format("~n")
        end,
        LM
    ).

print_set(Set) when is_map(Set) ->
    io:put_chars("("),
    print_setlist(lists:sort(maps:keys(Set))),
    io:put_chars(")");
print_set(Set) ->
    io:format("~w", [Set]).

print_setlist([]) ->
    ok;
print_setlist([H]) ->
    print_set(H);
print_setlist([H | T]) ->
    print_set(H),
    lists:foreach(
        fun(X) ->
            io:put_chars(","),
            print_set(X)
        end,
        T
    ).

deep_size(M) when is_map(M) ->
    maps:fold(
        fun(K, V, N) ->
            N + deep_size(K) + deep_size(V) + 1
        end,
        0,
        M
    );
deep_size(_) ->
    0.

% add value to multimap
-spec update_mmap(Key1, Key2, Map1, Value) -> Map2 when
    Map1 :: #{Key1 => #{Key2 => Value, _ => _}, _ => _},
    Map2 :: #{Key1 := #{Key2 := Value, _ => _}, _ => _}.
update_mmap(Key1, Key2, Map, Value) ->
    maps:update_with(Key1, fun(M) -> M#{Key2 => Value} end, #{Key2 => Value}, Map).

% call Fun(Key1, Value2, Key2, Value2) for every pair of a Key to Value
% associations in the map Map
% each_pair(Fun, Map) when is_map(Map) ->
%   each_pair(Fun, maps:iterator(Map));

% call Fun(Key1, Value2, Key2, Value2) for every pair of a Key to Value
% associations in the map represented by its iterator Iter
% each_pair(Fun, Iter) ->
%   case maps:next(Iter) of
%   {K, V, Iter_} ->
%     maps:foreach(fun (K_, V_) -> Fun(K, V, K_, V_) end, Iter_),
%     each_pair(Fun, Iter_);
%   none ->
%     ok
%   end.

% call Fun(Key1, Value2, Key2, Value2, Acc) for every pair of a Key to Value
% associations in the map Map in unspecified order
fold_pairs(Fun, Init, Map) when is_map(Map) ->
    fold_pairs(Fun, Init, maps:iterator(Map));
% call Fun(Key1, Value2, Key2, Value2, Acc) for every pair of a Key to Value
% associations in the map represented by its iterator Iter in unspecified order
fold_pairs(Fun, Init, Iter) ->
    case maps:next(Iter) of
        {K, V, Iter_} ->
            Acc_ =
                maps:fold(fun(K_, V_, Acc) -> Fun(K, V, K_, V_, Acc) end, Init, Iter_),
            fold_pairs(Fun, Acc_, Iter_);
        none ->
            Init
    end.

% tests

sample() ->
    [
        % [   b, c, d, e],  %  ->  b  c de  ->  b  cde
        % [a,    c, d, e],  %  ->  a  c de  ->  a  cde
        % [a, b,    d, e],  %  ->  ab   de  ==  ab  de
        % [a, b, c,    e],  %  ->  ab c  e  ->  abc  e
        % [a, b, c, d   ]   %  ->  ab c  d  ->  abc  d

        % [a, b, c, x, y, o, p, t],
        % [a, b, d, x, y, o, p, t],
        % [a, b, d, o, p, t],
        % [a, b, d, o, p, t]

        [1, 8, 1, 15, 6, 10, 9, 9, 14, 8],
        [14, 9, 10, 10, 14, 5, 12, 1],
        [12, 5, 6, 7, 11, 1, 8, 11],
        [3, 13, 9, 9, 5, 9],
        [5, 8, 6, 7, 3, 7, 12, 5, 11, 8],
        [11, 10, 1, 14, 1, 1, 12],
        [1, 2, 2, 15, 9],
        [8, 12, 8, 2, 10],
        [3, 5, 6, 12, 8, 15, 9, 12, 13, 12],
        [15, 12, 2, 1, 5, 14, 7, 10, 5],
        [4, 14, 3, 11, 13, 10, 2],
        [1, 10, 15, 14, 6, 12, 11, 7, 15, 2],
        [15, 9, 6, 9, 9, 11],
        [10, 3, 5, 11, 1, 5, 14, 11],
        [4, 12, 5, 7, 12, 4, 9, 8, 1, 14],
        [4, 12, 2, 8, 1, 3, 12],
        [4, 5, 4, 5, 7, 3, 13, 4],
        [10, 11, 15, 15, 7, 7, 12, 4, 5, 13],
        [3, 9, 12, 15, 10, 12, 6],
        [15, 8, 11, 9, 6, 13, 14, 3, 8, 15],
        [12, 3, 5, 1, 1, 7, 2, 13, 3],
        [12, 13, 9, 12, 12, 2, 15],
        [2, 5, 4, 9, 4, 7, 4, 9, 3, 5],
        [4, 15, 14, 8, 9, 6, 1, 12, 11, 1]

        % [a, b, c],
        % [a, b, c]
    ].

run() -> run(sample()).

run(L) ->
    % step 1 - enumerate sets
    {_, LM} = lists:foldl(
        fun(Elements, {SetId, Acc}) ->
            {SetId + 1, [{SetId, maps:from_keys(Elements, 1)} | Acc]}
        end,
        {1, []},
        L
    ),

    LM_ = reduce(LM),

    print("\nORIG:\n", lists:sort(LM)),

    print("\nSETS:\n", lists:sort(LM_)),

    ok.
