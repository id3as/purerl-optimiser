%%-------------
%% Can run outside of build tools with a command line such as:
%%
%% erlc -pa ../purerl-optimiser/_build/default/lib/purerl_optimiser/ebin -DPURERL_MEMOIZE=1 +'{parse_transform, purerl_optimiser}' +'{purerl_optimiser, #{math => #{booleanLike => [], intLike => ["Data.EuclideanRing.euclideanRingInt"], numberLike => ["Data.EuclideanRing.euclideanRingNumber"]}}}' server/output/Foo.Bar/foo_bar@ps.erl
%%-------------
-module(purerl_optimiser).

-export([ parse_transform/2
        , purs_type_to_erl/1
        , walk/3
        , modify/4
        , preIdentity/2
        , postIdentity/2
        ]).

-include("../include/purerl_optimiser.hrl").

parse_transform(Forms = [{attribute, _, file, _}, {attribute, _, module, Module} | _], CompileOptions) ->

  TransformOptions = proplists:get_value(purerl_optimiser, CompileOptions, #{}),

  case is_purs(Module) of
    true ->
      put('__module', Module),
      Final = lists:foldl(fun(Fn, Acc) ->
                              Fn(Acc)
                          end,
                          Forms,
                          [ fun optimise_discard/1
                          , fun optimise_newtype/1
                          , fun optimise_unsafeCoerce/1
                          , fun(F) -> optimise_math(F, TransformOptions) end
                          , fun inline/1
                          , fun unmemoise/1
                          , fun unroll/1
                          , fun effectfull_funs/1
                          , fun(F) -> memoise_terms(F, Module) end
                          ]
                         ),

      %% Debug output...
      case os:getenv("PURS_OPTIMISER_DEBUG") of
        xfalse ->
          ok;
        _ ->
          filelib:ensure_dir("/tmp/purs_optimiser/foo.txt"),
          _ = file:delete("/tmp/purs_optimiser/" ++ atom_to_list(Module) ++ ".erl"),
          file:write_file("/tmp/purs_optimiser/" ++ atom_to_list(Module) ++ ".forms-in", io_lib:format("~p~n.", [Forms])),
          file:write_file("/tmp/purs_optimiser/" ++ atom_to_list(Module) ++ ".forms-out", io_lib:format("~p~n.", [Final])),
          lists:foreach(fun(Form) ->
                            ok = file:write_file("/tmp/purs_optimiser/" ++ atom_to_list(Module) ++ ".erl", erl_pp:form(Form, [{indent, 2}, {linewidth, 120}]), [append]),
                            ok
                        end,
                        Final)
      end,

      Final;
    _ ->
      Forms
  end;

parse_transform(Forms, _Options) ->
  Forms.

%%------------------------------------------------------------------------------
%%-- Discard - replace control_bind.discard(discardUnit) with just a bind
optimise_discard(Forms) ->
  {NewForms, _} = modify(Forms, fun optimise_discard_form/2, fun postIdentity/2, undefined),
  NewForms.

optimise_discard_form(_Form = ?match_call(?local_call('memoize'),
                                          [?match_call(?remote_call('control_bind@ps', discard), [?match_call(?remote_call('control_bind@ps', discardUnit), []),
                                                                                                  BindDict
                                                                                                 ]
                                                      )
                                          ]),
                     State) ->
  NewForm = ?make_call(?make_local_call(memoize), [?make_call(?make_remote_call('control_bind@ps', 'bind'), [BindDict])]),
  {replace, NewForm, State};

optimise_discard_form(_Form, State) ->
  {continue, State}.

%%------------------------------------------------------------------------------
%%-- Remove newtype over / lens over
optimise_newtype(Forms) ->
  NewtypeFns = walk(Forms, fun gather_newtype_fns/2, #{removeFromCompose => []}),
  {NewForms, _} = modify(Forms, fun preIdentity/2, fun optimise_newtype_form/2, NewtypeFns),
  NewForms.

gather_newtype_fns(?match_function(Name, 0, [?match_clause([], [], [?match_call(?local_call(memoize),
                                                                                [ ?match_call(?remote_call('data_lens_iso_newtype@ps', '_Newtype'),
                                                                                              [?match_atom(undefined),
                                                                                               ?match_atom(undefined),
                                                                                               ?match_call(?remote_call('data_profunctor@ps', 'profunctorFn'), [])
                                                                                              ])
                                                                                ]
                                                                               )])]),
                   Acc = #{removeFromCompose := Remove}) ->
  Acc#{lensNewtype => Name,
       removeFromCompose => [Name | Remove]};

gather_newtype_fns(?match_function(Name, 0, [?match_clause([], [], [?match_call(?local_call(memoize),
                                                                                [ ?match_call(?remote_call('data_newtype@ps', 'unwrap'),
                                                                                              [?match_atom(undefined)
                                                                                              ])
                                                                                ]
                                                                               )])]),
                   Acc = #{removeFromCompose := Remove}) ->
  Acc#{removeFromCompose => [Name | Remove]
      , unwrap => Name};

gather_newtype_fns(?match_function(Name, 0, [?match_clause([], [], [?match_call(?local_call(memoize),
                                                                                [ ?match_call(?remote_call('data_newtype@ps', 'wrap'),
                                                                                              [?match_atom(undefined)
                                                                                              ])
                                                                                ]
                                                                               )])]),
                   Acc = #{removeFromCompose := Remove}) ->
  Acc#{removeFromCompose => [Name | Remove]};

gather_newtype_fns(?match_function(Name, 0, [?match_clause([], [], [?match_call(?local_call(memoize),
                                                                                [ ?match_call(?remote_call('control_semigroupoid@ps', 'compose'),
                                                                                              [?match_call(?remote_call('control_semigroupoid@ps', 'semigroupoidFn'), [])
                                                                                              ])
                                                                                ]
                                                                               )])]),
                   Acc) ->
  maps:put(compose, Name, Acc);

gather_newtype_fns(_Form, Acc) ->
  Acc.

%% Optimise `Data.Newtype.Over`
optimise_newtype_form(_Form =
                        ?match_call(
                           ?match_call(
                              ?match_call(?local_call('memoize'),
                                          [?match_call(?remote_call('data_newtype@ps', over), [?match_atom(undefined), ?match_atom(undefined)])
                                          ]),
                              [?match_call(?remote_call(_Mod, _Fn), [])]
                             ),
                           [Call]
                          ),
                     State) ->
  {Call, State};

%% Optimise `Data.Lens.Setter.Over _Newtype`
optimise_newtype_form(_Form =
                     ?match_call(?remote_call('data_lens_setter@ps', 'over'),
                                 [ ?match_call(?local_call(Name), [])
                                 , Arg1
                                 , Arg2
                                 ]
                                ),
                   State = #{lensNewtype := Name}) ->
  {?make_call(Arg1, [Arg2]), State};

%% %% Optimise `Data.Lens.Setter.Over _ unwrap` - e.g over MyNewtype unwrap x -> x
%% optimise_newtype_form(_Form =
%%                      ?match_call(?remote_call('data_lens_setter@ps', 'over'),
%%                                  [ ?match_call(?local_call(_), [])
%%                                  , ?match_call(?local_call(Name), [])
%%                                  , Arg2
%%                                  ]
%%                                 ),
%%                    State = #{unwrap := Name}) ->
%%   {Arg2, State};

%% %% As above, but when curried - e.g, map (over MyNewtype unwrap) l -> map identity l - we strip out `map identity` elsewhere...
%% optimise_newtype_form(_Form =
%%                         ?match_call(
%%                            ?match_call(
%%                               ?match_call(?remote_call('data_lens_setter@ps', 'over'), []),
%%                               [?match_call(?local_call(_), [])]
%%                              ),
%%                            [?match_call(?local_call(Name), [])]
%%                           ),
%%                    State = #{unwrap := Name}) ->
%%   {?make_lambda([?make_clause([?make_var('X')], [], [?make_var('X')])]), State};

%% Optimise composition with wrap / unwrap / _Newtype
optimise_newtype_form(Form = ?match_call(
                                ?match_call(?match_call(?local_call(Compose), []),
                                            [Other1 = ?match_call(?local_call(Fn1), [])]
                                           ),
                                [Other2 = ?match_call(?local_call(Fn2), [])]
                               ),
                      State = #{compose := Compose,
                                removeFromCompose := Remove}) ->
  case lists:member(Fn1, Remove) of
    true ->
      {Other2, State};
    false ->
      case lists:member(Fn2, Remove) of
        true ->
          {Other1, State};
        false ->
          {Form, State}
      end
  end;

optimise_newtype_form(Form = ?match_call(
                                ?match_call(?match_call(?local_call(Compose), []),
                                            [?match_call(?local_call(Fn), [])]
                                           ),
                                [Other]
                               ),
                      State = #{compose := Compose,
                                removeFromCompose := Remove}) ->
  case lists:member(Fn, Remove) of
    true ->
      {Other, State};
    false ->
      {Form, State}
  end;

optimise_newtype_form(Form = ?match_call(
                                ?match_call(?match_call(?local_call(Compose), []),
                                            [Other]
                                           ),
                                [?match_call(?local_call(Fn), [])]
                               ),
                      State = #{compose := Compose,
                                removeFromCompose := Remove}) ->
  case lists:member(Fn, Remove) of
    true ->
      {Other, State};
    false ->
      {Form, State}
  end;

optimise_newtype_form(Form, State) ->
  {Form, State}.

%%------------------------------------------------------------------------------
%%-- Remove unsafeCoerce
optimise_unsafeCoerce(Forms) ->
  GlobalBindings = walk(Forms, fun(Form, Acc) -> gather_global_unsafecoerce_bindings(Form, Acc) end, #{}),
  {NewForms, _} = modify(Forms, fun optimise_unsafeCoerce_forms/2, fun postIdentity/2, GlobalBindings),
  NewForms.

%% think this one is already done by purerl - unsafeCoerce x
optimise_unsafeCoerce_forms(_Form = ?match_call(?remote_call('unsafe_coerce@ps', unsafeCoerce), [Arg]), State) ->
  NewForm = Arg,
  {replace, NewForm, State};

%% but this isn't -
%% let foo = unsafeCoerce
%% foo x
optimise_unsafeCoerce_forms(FunForm = ?match_function(_Name, _Arity, Clauses), GlobalBindings) ->

  LocalBindings = walk(Clauses, fun(Form, Acc) -> gather_local_unsafecoerce_bindings(Form, Acc) end, #{}),

  {NewForm, _} = modify(FunForm, fun optimise_unsafeCoerce_funs/2, fun postIdentity/2, {GlobalBindings, LocalBindings}),

  {replace, NewForm, GlobalBindings};

optimise_unsafeCoerce_forms(_Form, State) ->
  {continue, State}.

optimise_unsafeCoerce_funs(?match_clause(Args, Guards, Body), State) ->
  {NewBody, _} = modify(Body, fun optimise_unsafeCoerce_remove_calls/2, fun postIdentity/2, State),

  {replace, ?make_clause(Args, Guards, NewBody), State};

optimise_unsafeCoerce_funs(_Form, State) ->
  {continue, State}.

optimise_unsafeCoerce_remove_calls(_Form = ?match_call(?match_var(Var), [Arg]), State = {_, LocalBindings}) ->
  case maps:is_key(Var, LocalBindings) of
    true ->
      {replace, Arg, State};
    false ->
      {continue, State}
  end;

optimise_unsafeCoerce_remove_calls(_Form = ?match_call(?local_call(Name), [Arg]), State = {GlobalBindings, _}) ->
  case maps:is_key(Name, GlobalBindings) of
    true ->
      {replace, Arg, State};
    false ->
      {continue, State}
  end;

optimise_unsafeCoerce_remove_calls(_Form, State) ->
  {continue, State}.

gather_local_unsafecoerce_bindings(?match_match(?match_var(Name),
                                          ?match_remote_fun(?match_atom(unsafe_coerce@ps), ?match_atom(unsafeCoerce), ?match_integer(1))), Acc) ->
  maps:put(Name, undefined, Acc);

gather_local_unsafecoerce_bindings(_Form, Acc) ->
  Acc.

gather_global_unsafecoerce_bindings(?match_function(Name, 0, [?match_clause([], [], [?match_remote_fun(?match_atom(unsafe_coerce@ps), ?match_atom(unsafeCoerce), ?match_integer(1))])]), Acc) ->
  maps:put(Name, undefined, Acc);

gather_global_unsafecoerce_bindings(_Form, Acc) ->
  Acc.

%%------------------------------------------------------------------------------
%%-- Math - spot the common math operators on Int and Number and replace
optimise_math(Forms, Options) ->

  #{ booleanLike := B
   , intLike := I
   , numberLike := N} = maps:get(math, Options, #{ booleanLike => []
                                                 , intLike => []
                                                 , numberLike => []
                                                 }),

  MathTypes = lists:foldl(fun({TypeName, Type}, Acc) ->
                              {TypeClassModule, TypeClass} = purs_type_to_erl(TypeName),
                              maps:put({TypeClassModule, TypeClass}, Type, Acc)
                          end,
                          #{},
                          lists:append( [ [{Item, boolean} || Item <- B]
                                        , [{Item, int} || Item <- I]
                                        , [{Item, number} || Item <- N]])),

  MathTerms = walk(Forms, fun(Form, Acc) -> gather_math_terms(Form, Acc, MathTypes) end, #{}),

  {NewForms, _} = modify(Forms, fun preIdentity/2, fun optimise_math_form/2, MathTerms),
  NewForms.

gather_math_terms({function, _, Name, 0, [?match_clause([], [], [ ?match_call(?local_call(memoize),
                                                                              [ ?match_call(?remote_call(MathModule, Operator),
                                                                                            [?match_call(?remote_call(TypeClassModule, TypeClass), [])])
                                                                              ]
                                                                             )
                                                                ])
                                         ]}, Acc, MathTypes)
  when (((MathModule == 'data_ord@ps') andalso ((Operator == lessThan) orelse (Operator == lessThanOrEq) orelse (Operator == greaterThan) orelse (Operator == greaterThanOrEq) orelse (Operator == min) orelse (Operator == max)))
        orelse
        ((MathModule == 'data_semiring@ps') andalso ((Operator == add) orelse (Operator == mul)))
        orelse
        ((MathModule == 'data_ring@ps') andalso ((Operator == sub)))
        orelse
        ((MathModule == 'data_euclideanRing@ps') andalso ((Operator == 'div')))
        orelse
        ((MathModule == 'data_euclideanRing@ps') andalso ((Operator == 'mod')))
        orelse
        ((MathModule == 'data_eq@ps') andalso ((Operator == 'eq')))
        orelse
        ((MathModule == 'data_heytingAlgebra@ps') andalso ((Operator == 'conj') orelse (Operator == 'disj')))
       ) ->
  case maps:find({TypeClassModule, TypeClass}, MathTypes) of
    {ok, Type} ->
      maps:put(Name, {Operator, Type}, Acc);
    error ->
      Acc
  end;

gather_math_terms(_Form, Acc, _MathOptions) ->
  Acc.

optimise_math_form(Form = ?match_call(
                             ?match_call(
                                ?match_call(?local_call(MaybeMathFun), []),
                                [Arg1]
                               ),
                             [Arg2]), State) ->

  case maps:find(MaybeMathFun, State) of
    error ->
      {Form, State};
    {ok, {Operator, Type}} ->

      Change = case Operator of
                 lessThan -> {op, '<'};
                 lessThanOrEq -> {op, '=<'};
                 greaterThan -> {op, '>'};
                 greaterThanOrEq -> {op, '>='};
                 min -> {call, ?make_call(?make_remote_call(erlang, min), [Arg1, Arg2])};
                 max -> {call, ?make_call(?make_remote_call(erlang, max), [Arg1, Arg2])};
                 add -> {op, '+'};
                 mul -> {op, '*'};
                 sub -> {op, '-'};
                 eq -> {op, '=='};
                 conj -> {op, 'andalso'};
                 disj -> {op, 'orelse'};
                 'div' ->
                   case Type of
                     int -> {op, 'div'};
                     number -> {op, '/'}
                   end;
                 'mod' ->
                   case Type of
                     int -> {call, ?make_call(?make_remote_call('data_euclideanRing@foreign', intMod), [Arg1, Arg2])};
                     number -> {literal, {float, 0, 0.0}}
                   end
               end,

      NewForm = case Change of
                  {op, NewOperator} -> {op, 0, NewOperator, Arg1, Arg2};
                  {call, Fn} -> Fn;
                  {literal, Literal} -> Literal
                end,
      {NewForm, State}
  end;

optimise_math_form(Form, State) ->
  {Form, State}.

%%------------------------------------------------------------------------------
%%-- Unmemoise - a precurse to unroll, unmemoising things that we want to unroll below...
unmemoise(Forms) ->
  {_, UnmemoiseMap} = modify(Forms, fun unmemoise_form/2, fun postIdentity/2, #{}),

  {Forms, UnmemoiseMap}.

unmemoise_form(?match_function(Name, 0, [?match_clause([], [],
                                                       [?match_call(
                                                           ?local_call(memoize),
                                                           [?match_call(?remote_call('data_foldable@ps', AllOrAny),
                                                                        [?match_call(?remote_call('erl_data_list_types@ps', 'foldableList'), []),
                                                                         ?match_call(?remote_call('data_heytingAlgebra@ps', 'heytingAlgebraBoolean'), [])
                                                                        ]
                                                                       )
                                                           ]
                                                          )
                                                       ]
                                                       )
                                        ]), State) when AllOrAny == all orelse AllOrAny == any ->

  Replacement = ?make_remote_call(lists, AllOrAny),

  {continue, maps:put(Name, Replacement, State)};

unmemoise_form(_Form, State) ->
  {continue, State}.

%%------------------------------------------------------------------------------
%%-- Inline - we are looking for things like
%%-- X = erl_data_map@ps:lookup(A, B),
%%-- case X of
%%--   bla
%%-- where X is not used in any other places in the function
%%-- When we fine it, we inline it to `case erl_data_map...`, at which point
%%-- unroll may well turn it into a direct call to map:find
inline(Forms) ->
  {NewForms, _} = modify(Forms, fun preIdentity/2, fun inline_form/2, 0),
  NewForms.

inline_form(_Form = ?match_clause(Args, Guards, Body), State) ->
  Body2 = inline_uncons(Body),
  Body3 = inline_lookup(Body2),
  {?make_clause(Args, Guards, Body3), State};

inline_form(_Form = ?match_block(Body), State) ->
  Body2 = inline_uncons(Body),
  Body3 = inline_lookup(Body2),
  {?make_block(Body3), State};

inline_form(Form, State) ->
  {Form, State}.

inline_uncons([Match = ?match_match(?match_var(Var), Call) | T]) ->
  CanInline = case Call of
                ?match_call(?remote_call('erl_data_list_types@ps', uncons), [_List]) -> true;
                ?match_call(?remote_call('erl_data_list@ps', head), [_List]) -> true;
                ?match_call(?remote_call('erl_data_map@ps', lookup), [_Key, _Map]) -> true;
                _ -> false
              end,

  if
    CanInline ->
      case walk(T, fun(Form, Acc) -> inline_count_var(Var, Form, Acc) end, 0) of
        1 ->
          %% We can do it
          {Inlined, _} = modify(T, fun preIdentity/2, fun inline_var/2, {Call, Var}),
          inline_uncons(Inlined);
        _N ->
          %% Nope, variable is reused
          [Match | inline_uncons(T)]
      end;
    true ->
      [Match | inline_uncons(T)]
  end;

inline_uncons([H | T]) ->
  [H | inline_uncons(T)];

inline_uncons([]) ->
  [].

inline_lookup([Match = ?match_match(?match_var(Var), Call = ?match_call(?remote_call('erl_data_map@ps', lookup), [_Key, _Map]))
               | T]) ->
  case walk(T, fun(Form, Acc) -> inline_count_var(Var, Form, Acc) end, 0) of
    1 ->
      %% We can do it
      {Inlined, _} = modify(T, fun preIdentity/2, fun inline_var/2, {Call, Var}),
      inline_lookup(Inlined);
    _N ->
      %% Nope, variable is reused
      [Match | inline_lookup(T)]
  end;

inline_lookup([H | T]) ->
  [H | inline_lookup(T)];

inline_lookup([]) ->
  [].

inline_count_var(Var, ?match_var(Var), N) ->
  N + 1;
inline_count_var(_, _, N) ->
  N.

inline_var(_Form = ?match_var(Var), State = {Call, Var}) ->
  {Call, State};
inline_var(Form, State) ->
  {Form, State}.

%%------------------------------------------------------------------------------
%%-- Unroll
-record(unroll_state,
       { unmemoise_map
       , n
       }).

unroll({Forms, UnmemoiseMap}) ->
  {NewForms, _} = modify(Forms, fun unroll_form_down/2, fun unroll_form/2, #unroll_state{unmemoise_map = UnmemoiseMap, n = 0}),
  NewForms.

%% case Map.lookup x of Just j -> jjj; Nothing -> nnn
unroll_form_down(_Form = ?match_case(?match_call(?remote_call('erl_data_map@ps', lookup), [Key, Map]), Clauses), State) ->

  try
    Clauses2 = [unroll_lookup_clause(Match, Guards, Body) || ?match_clause([Match], Guards, Body) <- Clauses],
    NewForm = ?make_case(?make_call(?make_remote_call(maps, find), [Key, Map]), Clauses2),
    {replace_and_continue, NewForm, State}
  catch _:_ ->
      io:format(user, "~p: Unrolling map lookup - failed to deal with ~p~n", [get('__module'), Clauses]),
      {continue, State}
  end;

unroll_form_down(_Form, State) ->
  {continue, State}.

unroll_form(Form = ?match_call(
                       ?match_call(
                          ?match_call(?local_call(Name), []),
                          [Arg1]),
                       [Arg2]),
            State) ->

  case maps:find(Name, State#unroll_state.unmemoise_map) of
    error ->
      {Form, State};
    {ok, Replacement} ->
      {?make_call(Replacement, [Arg1, Arg2]), State}
  end;

%% case List.head.lookup x of Just j -> jjj; Nothing -> nnn
unroll_form(Form = ?match_case(?match_call(?remote_call('erl_data_list@ps', head), [List]), Clauses), State) ->
  try
    Clauses2 = [unroll_head_clause(Match, Guards, Body) || ?match_clause([Match], Guards, Body) <- Clauses],
    NewForm = ?make_case(List, Clauses2),
    {NewForm, State}
  catch _:_ ->
      io:format(user, "~p: Unrolling list head - failed to deal with ~p~n", [get('__module'), Clauses]),
      {Form, State}
  end;

unroll_form(Form = ?match_case(?match_call(?remote_call('erl_data_list_types@ps', uncons), [List]),
                                Clauses
                               ), State) ->
  try
    Clauses2 = [unroll_uncons_clause(Match, Guards, Body) || ?match_clause([Match], Guards, Body) <- Clauses],
    NewForm = ?make_case(List, Clauses2),
    {NewForm, State}
  catch _:_ ->
      io:format(user, "~p: Unrolling list uncons - failed to deal with ~p~n", [get('__module'), Clauses]),
      {Form, State}
  end;

unroll_form(Form = ?match_case(?match_tuple([]), _Clauses), State) ->
  {Form, State};

unroll_form(_Form = ?match_case(?match_tuple(Elements), Clauses), State) ->
  {Elements2, Clauses2} = unroll_tuple_clauses(Elements, Clauses),
  {?make_case(?make_tuple(Elements2), Clauses2), State};

unroll_form(_Form = ?match_call(?remote_call('erl_data_map@ps', insert), [Key, Value, Map]), State) ->
  {{map, 0, Map, [{map_field_assoc, 0, Key, Value}]}, State};

unroll_form(_Form = ?match_call(?remote_call('erl_data_map@ps', lookup), [Key, Map]), State = #unroll_state{n = N}) ->

  Var = list_to_atom("__@M" ++ integer_to_list(N)),
  {?make_case(?make_call(?make_remote_call(maps, find), [Key, Map]),
              [ ?make_clause([?make_tuple([?make_atom(ok), ?make_var(Var)])], [], [?make_tuple([?make_atom(just), ?make_var(Var)])])
              , ?make_clause([?make_atom(error)], [], [?make_tuple([?make_atom(nothing)])])
              ]), State#unroll_state{n = N + 1}};

unroll_form(_Form = ?match_call(?remote_call('data_maybe@ps', 'fromMaybe\''),
                                 [DefaultFn, Value]),
             State = #unroll_state{n = N}) ->

  Var = list_to_atom("__@M" ++ integer_to_list(N)),
  {?make_case(Value, [ ?make_clause([?make_tuple([?make_atom(nothing)])], [], [?make_call(DefaultFn, [?make_atom(unit)])])
                              , ?make_clause([?make_tuple([?make_atom(just), ?make_var(Var)])], [], [?make_var(Var)])
                              ]), State#unroll_state{n = N + 1}};

unroll_form(_Form = ?match_call(
                        ?match_call(_Call = ?remote_call(Module, Fn), []),
                        [Arg1]),
             State = #unroll_state{n = N})
  when (Module == 'data_either@ps' andalso Fn == 'Left') orelse
       (Module == 'data_either@ps' andalso Fn == 'Right') ->

  EitherType = case Fn of
                 'Left' -> left;
                 'Right' -> right
               end,
  {?make_tuple([?make_atom(EitherType), Arg1]), State#unroll_state{n = N + 1}};

unroll_form(_Form = ?match_call(_Call = ?remote_call('foreign@ps', 'unsafeFromForeign'), [Arg]),
             State) ->
  {Arg, State};

unroll_form(_Form = ?match_call(?remote_call('control_monad_reader_trans@ps', 'runReaderT'),
                                [Fn, Context]
                               ), State) ->
  {?make_call(Fn, [Context]), State};

unroll_form(Form, State) ->
  {Form, State}.

%% we have a list of the tuple elements in `case {a, b, c} of`, and a list of the clauses.  Each clause *must* also be a tuple of the same arity -
%% clauses that are not tuples (e.g., a catch all) will cause us to not optimise the case statement
unroll_tuple_clauses(Elements, Clauses) ->
  try
    {ClausesArgs, ClausesGuards, ClausesBodies} =
      lists:unzip3([{ClauseArgs, ClauseGuards, ClauseBody} || ?match_clause([?match_tuple(ClauseArgs)], ClauseGuards, ClauseBody) <- Clauses]),

    if length(Clauses) /= length(ClausesArgs) -> throw(not_all_clauses_are_tuples);
       true -> ok
    end,

    {Elements2, Clauses2} = unroll_tuple_clauses_(Elements, ClausesArgs, ClausesGuards, ClausesBodies, [], [[] || _ <- Clauses]),

    {Elements2, Clauses2}
  catch
    A:B:S ->
      io:format(user, "~p: Unrolling tuple clauses failed to deal with ~p / ~p~n  due to ~p / ~p~n  at ~p~n", [get('__module'), Elements, Clauses, A, B, S]),
      {Elements, Clauses}
  end.

unroll_tuple_clauses_([], _ClausesArgs, ClausesGuards, ClausesBodies, ElementsAcc, ArgsAcc) ->
  %% ClausesArgs will be a list where every element is the empty list
  {lists:reverse(ElementsAcc), [?make_clause([?make_tuple(Args)], Guards, Body) || {Args, Guards, Body} <- lists:zip3([lists:reverse(Args) || Args <- ArgsAcc], ClausesGuards, ClausesBodies)]};

unroll_tuple_clauses_([HElement | TElements], ClausesArgs, ClausesGuards, ClausesBodies, ElementsAcc, ArgsAcc) ->

  {ThisElementArgs, RemainingArgs} = lists:unzip([{H, T} || [H | T] <- ClausesArgs]),

  {NewHeadElement, NewThisElementArgs, NewClausesGuards, NewClausesBodies} = unroll_tuple_clauses__(HElement, ThisElementArgs, ClausesGuards, ClausesBodies),

  NewArgsAcc = [[New | Acc] || {New, Acc} <- lists:zip(NewThisElementArgs, ArgsAcc)],

  unroll_tuple_clauses_(TElements, RemainingArgs, NewClausesGuards, NewClausesBodies, [NewHeadElement | ElementsAcc], NewArgsAcc).

unroll_tuple_clauses__(?match_call(?remote_call('erl_data_list_types@ps', uncons), [List]), ThisElementArgs, ClausesGuards, ClausesBodies) ->

  {NewThisElementArgs, NewClausesGuards, NewClausesBodies} = lists:unzip3([begin
     ?match_clause([NewArg], NewGuards, NewBody) = unroll_uncons_clause(Arg, Guards, Body),
     {NewArg, NewGuards, NewBody}
   end || {Arg, Guards, Body} <- lists:zip3(ThisElementArgs, ClausesGuards, ClausesBodies)
  ]),

  {List, NewThisElementArgs, NewClausesGuards, NewClausesBodies};

unroll_tuple_clauses__(ThisElement, ThisElementArgs, ClausesGuards, ClausesBodies) ->
  %% We don't know how to unroll this tuple element in the case
  {ThisElement, ThisElementArgs, ClausesGuards, ClausesBodies}.

%% Unroll clauses from an uncons...
%% Looking for clauses of the form: Nothing -> [anything]
unroll_uncons_clause(?match_tuple([?match_atom(nothing)]), Guards, Body) ->
    ?make_clause([?make_nil], Guards, Body);

%% Looking for clauses of the form: Just {head: H, tail: T} -> [anything]
%% In this case, H and T are exactly hd and tl of the erlang list, so we can just match on that
unroll_uncons_clause(?match_tuple([?match_atom(just),
                                   ?match_map([ ?map_field_exact(?match_atom(head), H)
                                              , ?map_field_exact(?match_atom(tail), T)
                                              ])]),
                     Guards, Body) ->
  ?make_clause([?make_cons(H, T)], Guards, Body);

%% Looking for clauses of the form: Just {head: H} -> [anything]
%% As above, just only capturing head
unroll_uncons_clause(?match_tuple([?match_atom(just),
                                   ?match_map([ ?map_field_exact(?match_atom(head), H)
                                              ])]),
                     Guards, Body) ->
  ?make_clause([?make_cons(H, ?make_var('_'))], Guards, Body);


%% Looking for clauses of the form: Just {tail: T} -> [anything]
%% As above, just only capturing tail
unroll_uncons_clause(?match_tuple([?match_atom(just),
                                   ?match_map([ ?map_field_exact(?match_atom(tail), T)
                                              ])]),
                     Guards, Body) ->
  ?make_clause([?make_cons(?make_var('_'), T)], Guards, Body);

%% Looking for clauses of the form: {just, Val} -> Val
%% This is capturing a non-empty list, but the {head, tail} record is being returned, so we need to make the map (and no guard in play)
unroll_uncons_clause(?match_tuple([?match_atom(just), ?match_var(L)]), [], [?match_var(L)]) ->
    H = list_to_atom("__H_" ++ atom_to_list(L)),
    T = list_to_atom("__T_" ++ atom_to_list(L)),
    ?make_clause([?make_cons(?make_var(H), ?make_var(T))], [], [?make_map([?make_map_field(?make_atom(head), ?make_var(H)), ?make_map_field(?make_atom(tail), ?make_var(T))])]);

%% Looking for clauses of the form: {just, Val} -> Val
%% This is capturing a non-empty list, but the {head, tail} record is potentially being used in the body, so we need to make the map as the first part of the body (also no guard in play)
unroll_uncons_clause(?match_tuple([?match_atom(just), ?match_var(L)]), [], Body) ->
    H = list_to_atom("__H_" ++ atom_to_list(L)),
    T = list_to_atom("__T_" ++ atom_to_list(L)),

    %% If the only reference to var(L) in the body is to do a maps:get(head) or a maps:get(tail), then we can drop those...
    {NewBody, _} = modify(Body, fun preIdentity/2, fun remove_head_tail_lookup/2, {L, H, T}),

    {NeedDict, _} = walk(NewBody, fun variable_is_used/2, {false, L}),

    NewBody2 = if
                 NeedDict -> [?make_match(?make_var(L), ?make_map([?make_map_field(?make_atom(head), ?make_var(H)), ?make_map_field(?make_atom(tail), ?make_var(T))]))
                             | NewBody
                             ];
                 true -> NewBody
               end,

    ?make_clause([?make_cons(?make_var(H), ?make_var(T))], [], NewBody2);

%% This is a catch-all, so we can just use it
unroll_uncons_clause(CatchAll = ?match_var('_'), Guards, Body) ->
  ?make_clause([CatchAll], Guards, Body).

%% Unroll clauses from a head...
unroll_head_clause(?match_tuple([?match_atom(just), Var]), [], JustBody) ->
  ?make_clause([?make_cons(Var, ?make_var('_'))], [], JustBody);

unroll_head_clause(?match_tuple([?match_atom(nothing)]), [], NothingBody) ->
  ?make_clause([?make_nil], [], NothingBody);

unroll_head_clause(CatchAll = ?match_var('_'), Guards, Body) ->
  ?make_clause([CatchAll], Guards, Body).

%% Unroll clauses from a map lookup
unroll_lookup_clause(?match_tuple([?match_atom(just), Var]), [], JustBody) ->
  ?make_clause([?make_tuple([?make_atom(ok), Var])], [], JustBody);

unroll_lookup_clause(?match_tuple([?match_atom(nothing)]), [], NothingBody) ->
  ?make_clause([?make_atom(error)], [], NothingBody);

unroll_lookup_clause(CatchAll = ?match_var('_'), Guards, Body) ->
  ?make_clause([CatchAll], Guards, Body).

remove_head_tail_lookup(?match_call(?remote_call('maps', 'get'), [?match_atom('head'), ?match_var(L)]), State = {L, H, _T}) ->
  {?make_var(H), State};

remove_head_tail_lookup(?match_call(?remote_call('maps','get'), [?match_atom('tail'), ?match_var(L)]), State = {L, _H, T}) ->
  {?make_var(T), State};

remove_head_tail_lookup(Form, State) ->
  {Form, State}.

variable_is_used(?match_var(L), {_, L}) ->
  {true, L};
variable_is_used(_, Acc) ->
  Acc.

%%------------------------------------------------------------------------------
%%-- Look for specific applications of effectful funs and rewrite then
effectfull_funs(Forms) ->
  {NewForms, _} = modify(Forms, fun preIdentity/2, fun effectfull_funs_form/2, undefined),
  NewForms.

effectfull_funs_form(_Form = ?match_call(?match_call(?remote_call('erl_process_raw@ps', send), Args), []), State) ->
  NewForm = ?make_call(?make_remote_call('erlang', 'send'), Args),
  {NewForm, State};

effectfull_funs_form(_Form = ?match_call(?match_call(?remote_call('erl_process_raw@ps', self), []), []), State) ->
  NewForm = ?make_call(?make_remote_call('erlang', 'self'), []),
  {NewForm, State};

effectfull_funs_form(_Form = ?match_call(?match_call(?remote_call('erl_process@ps', send), [To, Msg]), []), State) ->
  Replace = {op, 0, '!', To, Msg},
  {Replace, State};

effectfull_funs_form(_Form = ?match_call(?match_call(?remote_call('erl_kernel_erlang@ps', monotonicTime), []), []), State) ->
  Replace = ?make_call(?make_remote_call(erlang, monotonic_time), []),
  {Replace, State};

effectfull_funs_form(_Form = ?match_call(?match_call(?remote_call('erl_kernel_file@ps', read), [Handle, Amount]), []), State) ->
  Replace = ?make_call(?make_remote_call('erl_kernel_file@foreign', unsafeRead), [Handle, Amount]),
  {Replace, State};

effectfull_funs_form(Form, State) ->
  {Form, State}.

%%------------------------------------------------------------------------------
%%-- Memoisation - find instances of the memoize function and replace with lookups via persistent_term

%%------------------------------------------------------------------------------
%% https://github.com/purescript/purescript/issues/3926
%% https://github.com/purescript/purescript/pull/3915
-record(memoise_state,
        { module :: atom()
        , map = #{}
        }).

memoise_terms(Forms, Module) ->

  {NewForms, _} = modify(Forms, fun find_memoisable_terms/2, fun postIdentity/2, #memoise_state{module = Module}),

  {Modified, _} = modify(lists:flatten(NewForms), fun preIdentity/2, fun postIdentity/2, Module),

  Modified.


find_memoisable_terms(Form = {attribute, _, module, _Module}, State) ->
  %% Get the module name and add the export and on_load attributes
  Export = {attribute, 0, export, [{setupPersistentTerm, 0}]},
  OnLoad = {attribute, 0, on_load, {setupPersistentTerm, 0}},

  {replace, [Form, OnLoad, Export], State};

find_memoisable_terms(Form = {eof, _}, State = #memoise_state{map = TermMap}) ->

  Funs = lists:map(fun({Name, Args, Body}) ->
                       Key = case Args of
                               [] -> {atom, 0, Name};
                               _ -> {tuple, 0, [{atom, 0, Name} | Args]}
                             end,
                       {function, 0, Name, length(Args),
                        [
                         ?make_clause(Args, [],
                          [ {'try', 0,
                             [?make_call(?make_remote_call(persistent_term, get), [Key])],
                             [],
                             [?make_clause(
                               [ ?make_tuple([?make_var('_'), ?make_var('_'), ?make_var('_')]) ],
                               [ ],
                               [ {match, 0, ?make_var('X'), Body}
                               , {match, 0, ?make_var('Y'), ?make_call(?make_remote_call(persistent_term, put), [Key, {var, 0, 'X'}])}
                               %% , {match, 0, ?make_var('Y'), ?make_call(?make_remote_call(timer, tc), [?make_atom(persistent_term), ?make_atom(put), {cons, 0, Key, {cons, 0, {var, 0, 'X'}, {nil, 0}}}])}
                               %% , ?make_call(?make_remote_call(logger, notice), [{string, 0, "XXX HERE ~p/~p: ~p~n"}, {cons, 0, {atom, 0, Name}, {cons, 0, {integer, 0, length(Args)}, {cons, 0, ?make_var('Y'), {nil, 0}}}}])
                               , ?make_var('X')
                               ]
                              )
                             ],
                             []
                            }
                          ]
                         )
                        ]
                       }
                   end,
                   maps:values(TermMap)),

  SetupCalls = lists:filtermap(fun({Name, [], _Body}) ->
                                   {true, ?make_call(?make_atom(Name), [])};
                                  (_) ->
                                   false
                               end,
                               maps:values(TermMap)),

  SetupPersistentTerm = {function, 0, setupPersistentTerm, 0,
                         [
                          ?make_clause([], [],
                                       SetupCalls ++ [?make_atom('ok')]
                                      )
                         ]
                        },

  {replace, [SetupPersistentTerm, Funs, Form], State};

find_memoisable_terms(?match_call(?local_call('memoize'), [Call = ?match_call(Fn, _Args)]),
                      State = #memoise_state{map = Map, module = Module}) ->
  {Call2, Args, MemoArgs} = gather_free_variables(Call),

  {Key, _} = modify(Call2, fun preIdentity/2, fun remove_line_numbers/2, undefined),

  {TermName, State2} = case maps:find(Key, Map) of
                         error ->
                           Prefix = case Fn of
                                      ?match_call(?remote_call(_Module, FnName), _) -> atom_to_list(FnName);
                                      ?match_call(?local_call(FnName), _) -> atom_to_list(FnName);
                                      ?remote_call(_Module, FnName) -> atom_to_list(FnName);
                                      ?match_atom(FnName) -> atom_to_list(FnName);
                                      _ -> "unknown"
                                    end,
                           Name = list_to_atom("@memo_" ++ Prefix ++ "_" ++ atom_to_list(Module) ++ "_" ++ integer_to_list(maps:size(Map) + 1)),
                           Map2 = maps:put(Key, {Name, MemoArgs, Call2}, Map),
                           {Name, State#memoise_state{map = Map2}};
                         {ok, {Name, _, _}} ->
                           {Name, State}
                       end,

  MemoisedLookup = ?make_call(?make_local_call(TermName), Args),

  {replace, MemoisedLookup, State2};

find_memoisable_terms(_, State) ->
  {continue, State}.

remove_line_numbers(Form, State) when is_tuple(Form) ->
  {setelement(2, Form, 0), State};

remove_line_numbers(Form, State) ->
  {Form, State}.

-record(free_variables_state,
        { n = 0 :: integer
        , argsAcc = [] :: list(any())
        , memoArgsAcc = [] :: list(any())
        , inScope = sets:add_element('_', sets:new()) :: sets:set(any())
        , scopeStack = [] :: list(sets:set(any()))
        }).

gather_free_variables(Form) ->
  {Form2, #free_variables_state{argsAcc = Args, memoArgsAcc = MemoArgs}} = modify(Form, fun gather_free_variables_pre_/2, fun gather_free_variables_post_/2, #free_variables_state{}),
  {Form2, Args, MemoArgs}.

gather_free_variables_pre_(_Form = {clause, _, Variables, _Guards, _Body}, State = #free_variables_state{inScope = InScope, scopeStack = Stack}) ->
  {_, Variables2, _} = gather_free_variables(Variables),
  Names = [Name || {var, _, Name} <- Variables2],

  InScope2 = lists:foldl(fun(Name, Acc) -> sets:add_element(Name, Acc) end, InScope, Names),
  Stack2 = [InScope | Stack],
  {continue, State#free_variables_state{inScope = InScope2, scopeStack = Stack2}};

gather_free_variables_pre_(_Form = {match, _, Lhs, _Rhs}, State = #free_variables_state{inScope = InScope, scopeStack = Stack}) ->
  {_, Variables2, _} = gather_free_variables([Lhs]),
  Names = [Name || {var, _, Name} <- Variables2],

  InScope2 = lists:foldl(fun(Name, Acc) -> sets:add_element(Name, Acc) end, InScope, Names),
  Stack2 = [InScope | Stack],
  {continue, State#free_variables_state{inScope = InScope2, scopeStack = Stack2}};

gather_free_variables_pre_(_Form, State) ->
  {continue, State}.

gather_free_variables_post_(Form = {clause, _, _Variables, _Guards, _Body}, State = #free_variables_state{scopeStack = [_Prev | Stack]}) ->
  {Form, State#free_variables_state{scopeStack = Stack}};

gather_free_variables_post_(Form = {match, _, _Lhs, _Rhs}, State = #free_variables_state{scopeStack = [_Prev | Stack]}) ->
  {Form, State#free_variables_state{scopeStack = Stack}};

gather_free_variables_post_(Arg = {'var', Line, Name}, State = #free_variables_state{n = N, argsAcc = ArgsAcc, memoArgsAcc = MemoArgsAcc, inScope = InScope}) ->
  case sets:is_element(Name, InScope) of
    false ->
      MemoArg = {'var', Line, list_to_atom("_pursOptimize@" ++ integer_to_list(N))},
      {MemoArg, State#free_variables_state{n = N + 1, argsAcc = [Arg | ArgsAcc], memoArgsAcc = [MemoArg | MemoArgsAcc]}};
    true ->
      {Arg, State}
  end;

gather_free_variables_post_(Form, State) ->
  {Form, State}.

%%------------------------------------------------------------------------------
%%-- Helpers
is_purs(Module) ->
  case lists:reverse(atom_to_list(Module)) of
    [$s, $p, $@ | _] -> true;
    _ -> false
  end.

purs_type_to_erl(Type) ->
  Parts = string:split(Type, ".", all),
  purs_type_to_erl_(Parts, []).

purs_type_to_erl_([[H | Head], Type], Acc) ->
  {list_to_atom(lists:append(lists:reverse(["@ps", [string:to_lower(H) | Head] | Acc]))), list_to_atom(Type)};

purs_type_to_erl_([[H | Head] | Tail], Acc) ->
  purs_type_to_erl_(Tail, ["_", [string:to_lower(H) | Head] | Acc]).

preIdentity(_, State) -> {continue, State}.
postIdentity(X, State) -> {X, State}.

%%------------------------------------------------------------------------------
%%-- Walker
walk(List, Fun, State) when is_list(List) ->
  lists:foldl(fun(Item, InnerState) -> walk(Item, Fun, InnerState) end,
              State,
              List);

walk(Form = {clause, _Line, Args, Guards, Statements}, Fun, State) ->
  State2 = Fun(Form, State),
  State3 = walk(Args, Fun, State2),
  State4 = walk(Guards, Fun, State3),
  walk(Statements, Fun, State4);

walk(Form = {'case', _Line, Of, Clauses}, Fun, State) ->
  State2 = Fun(Form, State),
  State3 = walk(Of, Fun, State2),
  walk(Clauses, Fun, State3);

walk(Form = {'block', _Line, Statements}, Fun, State) ->
  State2 = Fun(Form, State),
  walk(Statements, Fun, State2);

walk(Form = {'receive', _Line, Clauses}, Fun, State) ->
  State2 = Fun(Form, State),
  walk(Clauses, Fun, State2);

walk(Form = {'match', _Line, Var, Statement}, Fun, State) ->
  State2 = Fun(Form, State),
  State3 = walk(Var, Fun, State2),
  walk(Statement, Fun, State3);

walk(Form = {'try', _Line, Exprs, Of, Catches, After}, Fun, State) ->
  State2 = Fun(Form, State),
  State3 = walk(Exprs, Fun, State2),
  State4 = walk(Of, Fun, State3),
  State5 = walk(Catches, Fun, State4),
  walk(After, Fun, State5);

walk(Form = {'call', _Line, Target, Args}, Fun, State) ->
  State2 = Fun(Form, State),
  State3 = walk(Target, Fun, State2),
  walk(Args, Fun, State3);

walk(Form = {'var', _Line, _Name}, Fun, State) ->
  Fun(Form, State);

walk(Form = {'op', _Line, _Operator, Lhs, Rhs}, Fun, State) ->
  State2 = Fun(Form, State),
  State3 = walk(Lhs, Fun, State2),
  walk(Rhs, Fun, State3);

walk(Form = {'op', _Line, _Operator, Lhs}, Fun, State) ->
  State2 = Fun(Form, State),
  walk(Lhs, Fun, State2);

walk(Form = {'integer', _Line, _Val}, Fun, State) ->
  Fun(Form, State);

walk(Form = {'float', _Line, _Val}, Fun, State) ->
  Fun(Form, State);

walk(Form = {'bin', _Line, _Value}, Fun, State) ->
  Fun(Form, State); %% todo

walk(Form = {'remote', _Line, {atom, _, _Module}, {atom, _, _Name}}, Fun, State) ->
  Fun(Form, State);

walk(Form = {'fun', _Line, {clauses, Clauses}}, Fun, State) ->
  State2 = Fun(Form, State),
  walk(Clauses, Fun, State2);

walk(Form = {'fun', _Line, {function, _Module, _Name, _Arity}}, Fun, State) ->
  Fun(Form, State);

walk(Form = {'fun', _Line, {function, _Name, _Arity}}, Fun, State) ->
  Fun(Form, State);

walk(Form = {'function', _Line, _Name, _, Body}, Fun, State) ->
  State2 = Fun(Form, State),
  walk(Body, Fun, State2);

walk(Form = {'named_fun', _Line, _Name, Clauses}, Fun, State) ->
  State2 = Fun(Form, State),
  walk(Clauses, Fun, State2);

walk(Form = {'tuple', _Line, Statements}, Fun, State) ->
  State2 = Fun(Form, State),
  walk(Statements, Fun, State2);

walk(Form = {'cons', _Line, Head, Tail}, Fun, State) ->
  State2 = Fun(Form, State),
  State3 = walk(Head, Fun, State2),
  walk(Tail, Fun, State3);

walk(Form = {'map', _Line, MapStatements}, Fun, State) ->
  State2 = Fun(Form, State),
  walk(MapStatements, Fun, State2);

walk(Form = {'map', _Line, Map, MapStatements}, Fun, State) ->
  State2 = Fun(Form, State),
  State3 = walk(Map, Fun, State2),
  walk(MapStatements, Fun, State3);

walk(Form = {'nil', _Line}, Fun, State) ->
  Fun(Form, State);

walk(Form = {'atom', _Line, _}, Fun, State) ->
  Fun(Form, State);

walk(Form = {'char', _Line, _}, Fun, State) ->
  Fun(Form, State);

walk(Form = {'eof', _Line}, Fun, State) ->
  Fun(Form, State);

walk(Form = {'attribute', _Line, _Attribute, _Value}, Fun, State) ->
  Fun(Form, State);

walk(Form = {'map_field_exact', _Line, Key, Value}, Fun, State) ->
  State2 = Fun(Form, State),
  State3 = walk(Key, Fun, State2),
  walk(Value, Fun, State3);

walk(Form = {'map_field_assoc', _Line, Key, Value}, Fun, State) ->
  State2 = Fun(Form, State),
  State3 = walk(Key, Fun, State2),
  walk(Value, Fun, State3).

%%------------------------------------------------------------------------------
%% Modifier
modify(List, PreFun, PostFun, State) when is_list(List) ->
  case PreFun(List, State) of
    {continue, State2} ->
      {Out, State3} = lists:foldl(fun(Item, {Acc, InnerState}) ->
                                      {Item2, InnerState2} = modify(Item, PreFun, PostFun, InnerState),
                                      {[Item2 | Acc], InnerState2}
                                  end,
                                  {[], State2},
                                  List),

      PostFun(lists:reverse(Out), State3);

    {replace, Value, State2} ->
      {Value, State2};
    {replace_and_continue, Value, State2} ->
      {Out, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun(Out, State3)
  end;

modify(Form = {attribute, _, _, _}, PreFun, PostFun, State) ->
  case PreFun(Form, State) of
    {continue, State2} ->
      PostFun(Form, State2);
    {replace, Value, State2} ->
      {Value, State2};
    {replace_and_continue, Value, State2} ->
      {Out, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun(Out, State3)
  end;

modify(Form = {function, Line, Name, Arity, Body}, PreFun, PostFun, State) ->
  case PreFun(Form, State) of
    {continue, State2} ->
      {Body2, State3} = modify(Body, PreFun, PostFun, State2),
      PostFun({function, Line, Name, Arity, Body2}, State3);
    {replace, Value, State2} ->
      {Value, State2};
    {replace_and_continue, Value, State2} ->
      {Out, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun(Out, State3)
  end;

modify(Form = {eof, _Line}, PreFun, PostFun, State) ->
  case PreFun(Form, State) of
    {continue, State2} ->
      PostFun(Form, State2);
    {replace, Value, State2} ->
      {Value, State2};
    {replace_and_continue, Value, State2} ->
      {Out, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun(Out, State3)
  end;

modify(Form = {clause, Line, Args, Guards, Statements}, PreFun, PostFun, State) ->
  case PreFun(Form, State) of
    {continue, State2} ->
      {Args2, State3} = modify(Args, PreFun, PostFun, State2),
      {Guards2, State4} = modify(Guards, PreFun, PostFun, State3),
      {Statements2, State5} = modify(Statements, PreFun, PostFun, State4),
      PostFun({clause, Line, Args2, Guards2, Statements2}, State5);
    {replace, Value, State2} ->
      {Value, State2};
    {replace_and_continue, Value, State2} ->
      {Out, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun(Out, State3)
  end;

modify(Form = {'case', Line, Of, Clauses}, PreFun, PostFun, State) ->
  case PreFun(Form, State) of
    {continue, State2} ->
      {Of2, State3} = modify(Of, PreFun, PostFun, State2),
      {Clauses2, State4} = modify(Clauses, PreFun, PostFun, State3),
      PostFun({'case', Line, Of2, Clauses2}, State4);
    {replace, Value, State2} ->
      {Value, State2};
    {replace_and_continue, Value, State2} ->
      {Out, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun(Out, State3)
  end;

modify(Form = {'block', Line, Statements}, PreFun, PostFun, State) ->
  case PreFun(Form, State) of
    {continue, State2} ->
      {Statements2, State3} = modify(Statements, PreFun, PostFun, State2),
      PostFun({'block', Line, Statements2}, State3);
    {replace, Value, State2} ->
      {Value, State2};
    {replace_and_continue, Value, State2} ->
      {Out, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun(Out, State3)
  end;

modify(Form = {'match', Line, Var, Statement}, PreFun, PostFun, State) ->
  case PreFun(Form, State) of
    {continue, State2} ->
      {Statement2, State3} = modify(Statement, PreFun, PostFun, State2),
      PostFun({'match', Line, Var, Statement2}, State3);
    {replace, Value, State2} ->
      {Value, State2};
    {replace_and_continue, Value, State2} ->
      {Out, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun(Out, State3)
  end;

modify(Form = {'call', Line, Target, Args}, PreFun, PostFun, State) ->
  case PreFun(Form, State) of
    {continue, State2} ->
      {Target2, State3} = modify(Target, PreFun, PostFun, State2),
      {Args2, State4} = modify(Args, PreFun, PostFun, State3),
      PostFun({'call', Line, Target2, Args2}, State4);
    {replace, Value, State2} ->
      {Value, State2};
    {replace_and_continue, Value, State2} ->
      {Out, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun(Out, State3)
  end;

modify(Form = {'var', Line, Name}, PreFun, PostFun, State) ->
  case PreFun(Form, State) of
    {continue, State2} ->
      PostFun({'var', Line, Name}, State2);
    {replace, Value, State2} ->
      {Value, State2};
    {replace_and_continue, Value, State2} ->
      {Out, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun(Out, State3)
  end;

modify(Form = {'op', Line, Operator, Lhs, Rhs}, PreFun, PostFun, State) ->
  case PreFun(Form, State) of
    {continue, State2} ->
      {Lhs2, State3} = modify(Lhs, PreFun, PostFun, State2),
      {Rhs2, State4} = modify(Rhs, PreFun, PostFun, State3),
      PostFun({'op', Line, Operator, Lhs2, Rhs2}, State4);
    {replace, Value, State2} ->
      {Value, State2};
    {replace_and_continue, Value, State2} ->
      {Out, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun(Out, State3)
  end;

modify(Form = {'op', Line, Operator, Lhs}, PreFun, PostFun, State) ->
  case PreFun(Form, State) of
    {continue, State2} ->
      {Lhs2, State3} = modify(Lhs, PreFun, PostFun, State2),
      PostFun({'op', Line, Operator, Lhs2}, State3);
    {replace, Value, State2} ->
      {Value, State2};
    {replace_and_continue, Value, State2} ->
      {Out, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun(Out, State3)
  end;

modify(Form = {'integer', Line, Val}, PreFun, PostFun, State) ->
  case PreFun(Form, State) of
    {continue, State2} ->
      PostFun({'integer', Line, Val}, State2);
    {replace, Value, State2} ->
      {Value, State2};
    {replace_and_continue, Value, State2} ->
      {Out, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun(Out, State3)
  end;

modify(Form = {'float', Line, Val}, PreFun, PostFun, State) ->
  case PreFun(Form, State) of
    {continue, State2} ->
      PostFun({'float', Line, Val}, State2);
    {replace, Value, State2} ->
      {Value, State2};
    {replace_and_continue, Value, State2} ->
      {Out, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun(Out, State3)
  end;

modify(Form = {'bin', Line, Val}, PreFun, PostFun, State) ->
  case PreFun(Form, State) of
    {continue, State2} ->
      PostFun({'bin', Line, Val}, State2); %% TODO - recurse on value?
    {replace, Value, State2} ->
      {Value, State2};
    {replace_and_continue, Value, State2} ->
      {Out, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun(Out, State3)
  end;

modify(Form = {'nil', Line}, PreFun, PostFun, State) ->
  case PreFun(Form, State) of
    {continue, State2} ->
      PostFun({'nil', Line}, State2);
    {replace, Value, State2} ->
      {Value, State2};
    {replace_and_continue, Value, State2} ->
      {Out, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun(Out, State3)
  end;

modify(Form = {'cons', Line, Head, Tail}, PreFun, PostFun, State) ->
  case PreFun(Form, State) of
    {continue, State2} ->
      {Head2, State3} = modify(Head, PreFun, PostFun, State2),
      {Tail2, State4} = modify(Tail, PreFun, PostFun, State3),
      PostFun({'cons', Line, Head2, Tail2}, State4);
    {replace, Value, State2} ->
      {Value, State2};
    {replace_and_continue, Value, State2} ->
      {Out, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun(Out, State3)
  end;

modify(Form = {'remote', Line, Module, Name}, PreFun, PostFun, State) ->
  case PreFun(Form, State) of
    {continue, State2} ->
      {Module2, State3} = modify(Module, PreFun, PostFun, State2),
      {Name2, State4} = modify(Name, PreFun, PostFun, State3),
      PostFun({'remote', Line, Module2, Name2}, State4);
    {replace, Value, State2} ->
      {Value, State2};
    {replace_and_continue, Value, State2} ->
      {Out, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun(Out, State3)
  end;

modify(Form = {'fun', Line, {clauses, Clauses}}, PreFun, PostFun, State) ->
  case PreFun(Form, State) of
    {continue, State2} ->
      {Clauses2, State3} = modify(Clauses, PreFun, PostFun, State2),
      PostFun({'fun', Line, {clauses, Clauses2}}, State3);
    {replace, Value, State2} ->
      {Value, State2};
    {replace_and_continue, Value, State2} ->
      {Out, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun(Out, State3)
  end;

modify(Form = {'fun', Line, {function, Module, Name, Arity}}, PreFun, PostFun, State) ->
  case PreFun(Form, State) of
    {continue, State2} ->
      PostFun({'fun', Line, {function, Module, Name, Arity}}, State2);
    {replace, Value, State2} ->
      {Value, State2};
    {replace_and_continue, Value, State2} ->
      {Out, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun(Out, State3)
  end;

modify(Form = {'fun', Line, {function, Name, Arity}}, PreFun, PostFun, State) ->
  case PreFun(Form, State) of
    {continue, State2} ->
      PostFun({'fun', Line, {function, Name, Arity}}, State2);
    {replace, Value, State2} ->
      {Value, State2};
    {replace_and_continue, Value, State2} ->
      {Out, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun(Out, State3)
  end;

modify(Form = {'named_fun', Line, Name, Clauses}, PreFun, PostFun, State) ->
  case PreFun(Form, State) of
    {continue, State2} ->
      {Clauses2, State3} = modify(Clauses, PreFun, PostFun, State2),
      PostFun({'named_fun', Line, Name, Clauses2}, State3);
    {replace, Value, State2} ->
      {Value, State2};
    {replace_and_continue, Value, State2} ->
      {Out, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun(Out, State3)
  end;

modify(Form = {'tuple', Line, Statements}, PreFun, PostFun, State) ->
  case PreFun(Form, State) of
    {continue, State2} ->
      {Statements2, State3} = modify(Statements, PreFun, PostFun, State2),
      PostFun({'tuple', Line, Statements2}, State3);
    {replace, Value, State2} ->
      {Value, State2};
    {replace_and_continue, Value, State2} ->
      {Out, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun(Out, State3)
  end;

modify(Form = {'map', Line, MapStatements}, PreFun, PostFun, State) ->
  case PreFun(Form, State) of
    {continue, State2} ->
      {MapStatements2, State3} = modify(MapStatements, PreFun, PostFun, State2),
      PostFun({'map', Line, MapStatements2}, State3);
    {replace, Value, State2} ->
      {Value, State2};
    {replace_and_continue, Value, State2} ->
      {Out, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun(Out, State3)
  end;

modify(Form = {'map', Line, Var, MapStatements}, PreFun, PostFun, State) ->
  case PreFun(Form, State) of
    {continue, State2} ->
      {Var2, State3} = modify(Var, PreFun, PostFun, State2),
      {MapStatements2, State4} = modify(MapStatements, PreFun, PostFun, State3),
      PostFun({'map', Line, Var2, MapStatements2}, State4);
    {replace, Value, State2} ->
      {Value, State2};
    {replace_and_continue, Value, State2} ->
      {Out, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun(Out, State3)
  end;

modify(Form = {'lc', Line, Item, Generators}, PreFun, PostFun, State) ->
  case PreFun(Form, State) of
    {continue, State2} ->
      {Item2, State3} = modify(Item, PreFun, PostFun, State2),
      {Generators2, State4} = modify(Generators, PreFun, PostFun, State3),
      PostFun({'lc', Line, Item2, Generators2}, State4);
    {replace, Value, State2} ->
      {Value, State2};
    {replace_and_continue, Value, State2} ->
      {Out, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun(Out, State3)
  end;

modify(Form = {'generate', Line, Var, Source}, PreFun, PostFun, State) ->
  case PreFun(Form, State) of
    {continue, State2} ->
      {Var2, State3} = modify(Var, PreFun, PostFun, State2),
      {Source2, State4} = modify(Source, PreFun, PostFun, State3),
      PostFun({'generate', Line, Var2, Source2}, State4);
    {replace, Value, State2} ->
      {Value, State2};
    {replace_and_continue, Value, State2} ->
      {Out, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun(Out, State3)
  end;

%% todo
modify(Form = {'try', Line, Call, Something, Clauses, SomethingElse}, PreFun, PostFun, State) ->
  case PreFun(Form, State) of
    {continue, State2} ->
      {Call2, State3} = modify(Call, PreFun, PostFun, State2),
      {Something2, State4} = modify(Something, PreFun, PostFun, State3),
      {Clauses2, State5} = modify(Clauses, PreFun, PostFun, State4),
      {SomethingElse2, State6} = modify(SomethingElse, PreFun, PostFun, State5),
      PostFun({'try', Line, Call2, Something2, Clauses2, SomethingElse2}, State6);
    {replace, Value, State2} ->
      {Value, State2};
    {replace_and_continue, Value, State2} ->
      {Out, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun(Out, State3)
  end;

modify(Form = {'receive', Line, Clauses}, PreFun, PostFun, State) ->
  case PreFun(Form, State) of
    {continue, State2} ->
      {Clauses2, State3} = modify(Clauses, PreFun, PostFun, State2),
      PostFun({'receive', Line, Clauses2}, State3);
    {replace, Value, State2} ->
      {Value, State2};
    {replace_and_continue, Value, State2} ->
      {Out, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun(Out, State3)
  end;

modify(Form = {'receive', Line, Clauses, Delay, After}, PreFun, PostFun, State) ->
  case PreFun(Form, State) of
    {continue, State2} ->
      {Clauses2, State3} = modify(Clauses, PreFun, PostFun, State2),
      {Delay2, State4} = modify(Delay, PreFun, PostFun, State3),
      {After2, State5} = modify(After, PreFun, PostFun, State4),
      PostFun({'receive', Line, Clauses2, Delay2, After2}, State5);
    {replace, Value, State2} ->
      {Value, State2};
    {replace_and_continue, Value, State2} ->
      {Out, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun(Out, State3)
  end;

modify(Form = {'record', Line, Name, Fields}, PreFun, PostFun, State) ->
  case PreFun(Form, State) of
    {continue, State2} ->
      {Fields2, State3} = modify(Fields, PreFun, PostFun, State2),
      PostFun({'record', Line, Name, Fields2}, State3);
    {replace, Value, State2} ->
      {Value, State2};
    {replace_and_continue, Value, State2} ->
      {Out, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun(Out, State3)
  end;

modify(Form = {'record', Line, Variable, Name, Fields}, PreFun, PostFun, State) ->
  case PreFun(Form, State) of
    {continue, State2} ->
      {Variable2, State3} = modify(Variable, PreFun, PostFun, State2),
      {Fields2, State4} = modify(Fields, PreFun, PostFun, State3),
      PostFun({'record', Line, Variable2, Name, Fields2}, State4);
    {replace, Value, State2} ->
      {Value, State2};
    {replace_and_continue, Value, State2} ->
      {Out, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun(Out, State3)
  end;

modify(Form = {'record_field', Line, Name, Value}, PreFun, PostFun, State) ->
  case PreFun(Form, State) of
    {continue, State2} ->
      {Value2, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun({'record_field', Line, Name, Value2}, State3);
    {replace, Val, State2} ->
      {Val, State2};
    {replace_and_continue, Value, State2} ->
      {Out, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun(Out, State3)
  end;

modify(Form = {'record_field', Line, Variable, Name, Value}, PreFun, PostFun, State) ->
  case PreFun(Form, State) of
    {continue, State2} ->
      {Variable2, State3} = modify(Variable, PreFun, PostFun, State2),
      {Value2, State4} = modify(Value, PreFun, PostFun, State3),
      PostFun({'record_field', Line, Variable2, Name, Value2}, State4);
    {replace, Val, State2} ->
      {Val, State2};
    {replace_and_continue, Value, State2} ->
      {Out, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun(Out, State3)
  end;

modify(Form = {'b_generate', Line, Bin, Source}, PreFun, PostFun, State) ->
  case PreFun(Form, State) of
    {continue, State2} ->
      {Source2, State3} = modify(Source, PreFun, PostFun, State2),
      PostFun({'b_generate', Line, Bin, Source2}, State3);
    {replace, Value, State2} ->
      {Value, State2};
    {replace_and_continue, Value, State2} ->
      {Out, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun(Out, State3)
  end;

modify(Form = {'if', Line, Clauses}, PreFun, PostFun, State) ->
  case PreFun(Form, State) of
    {continue, State2} ->
      {Clauses2, State3} = modify(Clauses, PreFun, PostFun, State2),
      PostFun({'if', Line, Clauses2}, State3);
    {replace, Value, State2} ->
      {Value, State2};
    {replace_and_continue, Value, State2} ->
      {Out, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun(Out, State3)
  end;

modify(Form = {'string', Line, String}, PreFun, PostFun, State) ->
  case PreFun(Form, State) of
    {continue, State2} ->
      PostFun({'string', Line, String}, State2);
    {replace, Value, State2} ->
      {Value, State2};
    {replace_and_continue, Value, State2} ->
      {Out, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun(Out, State3)
  end;

modify(Form = {'char', Line, Char}, PreFun, PostFun, State) ->
  case PreFun(Form, State) of
    {continue, State2} ->
      PostFun({'char', Line, Char}, State2);
    {replace, Value, State2} ->
      {Value, State2};
    {replace_and_continue, Value, State2} ->
      {Out, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun(Out, State3)
  end;

modify(Form = {'atom', Line, Atom}, PreFun, PostFun, State) ->
  case PreFun(Form, State) of
    {continue, State2} ->
      PostFun({'atom', Line, Atom}, State2);
    {replace, Value, State2} ->
      {Value, State2};
    {replace_and_continue, Value, State2} ->
      {Out, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun(Out, State3)
  end;

modify(Form = {'map_field_exact', Line, Key, Value}, PreFun, PostFun, State) ->
  case PreFun(Form, State) of
    {continue, State2} ->
      {Key2, State3} = modify(Key, PreFun, PostFun, State2),
      {Value2, State4} = modify(Value, PreFun, PostFun, State3),
      PostFun({'map_field_exact', Line, Key2, Value2}, State4);
    {replace, Value2, State2} ->
      {Value2, State2};
    {replace_and_continue, Value, State2} ->
      {Out, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun(Out, State3)
  end;

modify(Form = {'map_field_assoc', Line, Key, Value}, PreFun, PostFun, State) ->
  case PreFun(Form, State) of
    {continue, State2} ->
      {Key2, State3} = modify(Key, PreFun, PostFun, State2),
      {Value2, State4} = modify(Value, PreFun, PostFun, State3),
      PostFun({'map_field_assoc', Line, Key2, Value2}, State4);
    {replace, Value2, State2} ->
      {Value2, State2};
    {replace_and_continue, Value, State2} ->
      {Out, State3} = modify(Value, PreFun, PostFun, State2),
      PostFun(Out, State3)
  end.
